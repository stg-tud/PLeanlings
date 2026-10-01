/-
# 18.04 — Substitution algebra I: renamings

The heart of the proof (18.06) is the **fundamental lemma**: a well-typed
term with its free variables replaced by reducible terms is reducible.

    HasType Γ t T → (∀ x A, Γ[x]? = some A → R A (σ x)) → R T (subst σ t)

In its `λ` case we meet `subst σ (lam A t) = lam A (subst (exts σ) t)`. Applied
to a value `v`, it β-reduces to

    subst (subst1 v) (subst (exts σ) t)

while the induction hypothesis talks about `subst (scons v σ) t`, with the
substitution `scons v σ` that sends `0 ↦ v` and `n + 1 ↦ σ n`. We must show
that these two terms are **equal**. On paper this is "obvious"; with de Bruijn
indices it takes a small algebra of *fusion laws*, saying that two
consecutive renamings/substitutions can be merged into one:

    rename ρ (rename ρ' t) = rename (ρ ∘ ρ') t          (this file)
    subst σ  (rename ρ t)  = subst (σ ∘ ρ) t             (this file)
    rename ρ (subst σ t)   = subst (rename ρ ∘ σ) t      (this file)
    subst τ  (subst σ t)   = subst (subst τ ∘ σ) t       (18.05)

To avoid function extensionality, and to make the inductions go through, each
law takes the composed function as a separate argument with a *pointwise*
hypothesis, e.g.

    theorem rename_rename (h : ∀ x, ρ (ρ' x) = ρ'' x) :
        rename ρ (rename ρ' t) = rename ρ'' t

**Proof pattern.** Induction on `t`, generalizing all the functions. Every case
except `lam` is `simp` with the definitions and the induction hypotheses. In
the `lam` case, after `simp only [rename]` (or `[rename, subst]`) the goal is
the induction hypothesis for the *lifted* functions. `rw [ih]` reduces it to the
pointwise hypothesis for the lifted functions, which is a case distinction on
the variable: `0` is trivial, and `n + 1` follows from `h`.

In `rename_subst` the `n + 1` case is more interesting. After unfolding, you
must show

    rename (ext ρ) (rename Nat.succ (σ n)) = rename Nat.succ (rename ρ (σ n))

Both sides are `rename (fun x => ρ x + 1) (σ n)` by `rename_rename` (the
pointwise hypotheses hold by `rfl`, because `ext ρ (x + 1)` *is* `ρ x + 1`).
Tip: state these two equations with `have` and the explicit middle term; a bare
`rw [rename_rename (fun _ => rfl)]` lets Lean guess `ρ''`, and the guess
is often not what you want.

## Your task

1. Prove `subst_rename`. Its proof has the same shape as `rename_rename`.
2. Finish the `n + 1` case of `rename_subst`.
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

/-! ## Fusion laws for renaming -/

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
  sorry

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
      sorry
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]
