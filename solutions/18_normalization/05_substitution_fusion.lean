/-
# 18.05 — Substitution algebra II: substitutions

The last fusion law merges two substitutions:

    theorem subst_subst (h : ∀ x, subst τ (σ x) = υ x) :
        subst τ (subst σ t) = subst υ t

Same pattern as in 18.04. In the `lam` case, the `n + 1` subcase now reads

    subst (exts τ) (rename Nat.succ (σ n)) = rename Nat.succ (subst τ (σ n))

and both sides equal `subst (fun x => rename Nat.succ (τ x)) (σ n)`: the left
one by `subst_rename`, the right one by `rename_subst` (from 18.04), with
pointwise hypotheses by `rfl`.

We also need that substituting variables by themselves does nothing:

    theorem subst_id (h : ∀ x, σ x = .var x) : subst σ t = t

Now the payoff, the equation for the `λ` case of the fundamental lemma:

    theorem subst1_exts :
        subst (subst1 v) (subst (exts σ) t) = subst (scons v σ) t

By `subst_subst` it suffices to check, for every `x`,
`subst (subst1 v) (exts σ x) = scons v σ x`:

* `x = 0`: `exts σ 0 = var 0`, which becomes `v`. Both sides are `v`.
* `x = n + 1`: `exts σ (n + 1) = rename Nat.succ (σ n)`, and then
  `subst (subst1 v) (rename Nat.succ (σ n)) = subst var (σ n) = σ n`:
  first `subst_rename` (since `subst1 v (k + 1) = var k`), then `subst_id`.

Note that we never need "closed terms are unaffected by substitution". The
β-step substitutes into `subst (exts σ) t`, and `exts` already shifts `σ` out of
the way of the new variable `0`.

## Your task

1. Finish the `n + 1` case of `subst_subst`.
2. Prove `subst_id` (same pattern as the other fusion laws).
3. Prove `subst1_exts`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Types of this chapter: `T ::= bool | T ⇒ T` (no `nat`). -/
inductive Ty where
  | bool
  | arrow (A B : Ty)
  deriving DecidableEq, Repr

/-- `A ⇒ B` is the function type. It associates to the right. -/
infixr:70 " ⇒ " => Ty.arrow

/-- Terms with de Bruijn indices. `lam A t` binds variable `0` (of type `A`) in `t`. -/
inductive Term where
  | var (x : Nat)
  | lam (A : Ty) (body : Term)
  | app (f a : Term)
  | tru
  | fls
  | ite (c t e : Term)
  deriving DecidableEq, Repr

/-- Lift a renaming under a binder: `0` stays `0`, `n + 1` becomes `ρ n + 1`. -/
def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply the renaming `ρ` to all free variables. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .var x => .var (ρ x)
  | .lam A t => .lam A (rename (ext ρ) t)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)

/-- Lift a substitution under a binder. -/
def exts (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Parallel substitution: replace every free variable `x` by `σ x`. -/
def subst (σ : Nat → Term) : Term → Term
  | .var x => σ x
  | .lam A t => .lam A (subst (exts σ) t)
  | .app f a => .app (subst σ f) (subst σ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

theorem rename_rename {ρ ρ' ρ'' : Nat → Nat} {t : Term} (h : ∀ x, ρ (ρ' x) = ρ'' x) :
    rename ρ (rename ρ' t) = rename ρ'' t := by
  induction t generalizing ρ ρ' ρ'' with
  | var x => simp [rename, h]
  | lam A t ih =>
    simp only [rename]
    rw [ih]
    -- left: the lifted renamings still compose
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [ext, h]
  | app f a ihf iha => simp [rename, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, ihc h, iht h, ihe h]

theorem subst_rename {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}
    (h : ∀ x, σ (ρ x) = τ x) :
    subst σ (rename ρ t) = subst τ t := by
  induction t generalizing σ τ ρ with
  | var x => simp [rename, subst, h]
  | lam A t ih =>
    simp only [rename, subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [ext, exts, h]
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]

theorem rename_subst {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}
    (h : ∀ x, rename ρ (σ x) = τ x) :
    rename ρ (subst σ t) = subst τ t := by
  induction t generalizing σ τ ρ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [rename, subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n =>
      -- goal: rename (ext ρ) (exts σ (n + 1)) = exts τ (n + 1)
      simp only [exts, ← h n]
      have e1 : rename (ext ρ) (rename Nat.succ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
        rename_rename (fun _ => rfl)
      have e2 : rename Nat.succ (rename ρ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
        rename_rename (fun _ => rfl)
      rw [e1, e2]
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]

/-! ## Fusion laws for substitution -/

theorem subst_subst {σ τ υ : Nat → Term} {t : Term} (h : ∀ x, subst τ (σ x) = υ x) :
    subst τ (subst σ t) = subst υ t := by
  induction t generalizing σ τ υ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n =>
      -- goal: subst (exts τ) (exts σ (n + 1)) = exts υ (n + 1)
      simp only [exts, ← h n]
      have e1 : subst (exts τ) (rename Nat.succ (σ n)) = subst (fun x => rename Nat.succ (τ x)) (σ n) :=
        subst_rename (fun _ => rfl)
      have e2 : rename Nat.succ (subst τ (σ n)) = subst (fun x => rename Nat.succ (τ x)) (σ n) :=
        rename_subst (fun _ => rfl)
      rw [e1, e2]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [subst, ihc h, iht h, ihe h]

theorem subst_id {σ : Nat → Term} {t : Term} (h : ∀ x, σ x = .var x) : subst σ t = t := by
  induction t generalizing σ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [exts, h, rename]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [subst, ihc h, iht h, ihe h]

/-- `scons v σ` maps `0` to `v` and `n + 1` to `σ n`
(written `v · σ` on paper). -/
def scons (v : Term) (σ : Nat → Term) : Nat → Term
  | 0 => v
  | n + 1 => σ n

theorem subst1_exts {v : Term} {σ : Nat → Term} {t : Term} :
    subst (subst1 v) (subst (exts σ) t) = subst (scons v σ) t := by
  apply subst_subst
  intro x
  cases x with
  | zero => rfl
  | succ n =>
    show subst (subst1 v) (rename Nat.succ (σ n)) = σ n
    have e : subst (subst1 v) (rename Nat.succ (σ n)) = subst Term.var (σ n) :=
      subst_rename (fun _ => rfl)
    rw [e, subst_id (fun _ => rfl)]
