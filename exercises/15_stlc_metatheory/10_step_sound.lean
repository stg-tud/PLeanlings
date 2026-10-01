/-
# 15.10 — The interpreter is sound

The last piece connects the interpreter of 14.07 to the semantics: whenever
`step` takes a step, so does `Step`, and therefore `eval` only performs
legal reductions.

    theorem step_sound : step t = some t' → Step t t'
    theorem eval_star  : Star Step t (eval n t)

First a small lemma: `isValue t = true → Value t` (induction on `t`).

`step_sound` goes by induction on `t`, generalizing `t'`. The definition of
`step` uses `if … then … else` and `match`, and the tactic `split at h`
splits a hypothesis `h : (if c then x else y) = some t'` (or a `match`) into
one goal per branch. You get the condition as a new hypothesis, and you can name it
with `next hc => …`. For branches of the form `(step a).map … = some t'`, use
`cases hs : step a with | none => … | some a' => …` and `simp [hs] at h`.

`eval_star` is then an easy induction on the fuel.

## Your task

1. Prove `isValue_sound`.
2. Complete the `app` case of `step_sound` (the other cases show you how).
3. Prove `eval_star`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types: `T ::= bool | nat | T ⇒ T`. -/
inductive Ty where
  | bool
  | nat
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
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving DecidableEq, Repr

/-- A context lists the types of the free variables: `Γ[0]?` is the type of `var 0`. -/
abbrev Ctx := List Ty

/-- `HasType Γ t T` means `Γ ⊢ t : T`. -/
/-
    Γ[x]? = some A           A :: Γ ⊢ t : B             Γ ⊢ f : A ⇒ B    Γ ⊢ a : A
  ─────────────── var    ──────────────────── lam    ──────────────────────────── app
   Γ ⊢ var x : A          Γ ⊢ lam A t : A ⇒ B                Γ ⊢ app f a : B

  ───────────────── tru   ───────────────── fls
   Γ ⊢ tru : bool          Γ ⊢ fls : bool

   Γ ⊢ c : bool    Γ ⊢ t : A    Γ ⊢ e : A
  ───────────────────────────────────────── ite
          Γ ⊢ ite c t e : A

                         Γ ⊢ t : nat              Γ ⊢ t : nat             Γ ⊢ t : nat
  ───────────── zero   ───────────────── succ   ───────────────── pred  ──────────────────── iszero
   Γ ⊢ zero : nat       Γ ⊢ succ t : nat         Γ ⊢ pred t : nat       Γ ⊢ iszero t : bool
-/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (.var x) A
  | lam {Γ A t B} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ c t e A} : HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A
  | zero {Γ} : HasType Γ .zero .nat
  | succ {Γ t} : HasType Γ t .nat → HasType Γ (.succ t) .nat
  | pred {Γ t} : HasType Γ t .nat → HasType Γ (.pred t) .nat
  | iszero {Γ t} : HasType Γ t .nat → HasType Γ (.iszero t) .bool

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
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .pred t => .pred (rename ρ t)
  | .iszero t => .iszero (rename ρ t)

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
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .pred t => .pred (subst σ t)
  | .iszero t => .iszero (subst σ t)

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions, booleans and numerals. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls
  | zero : Value .zero
  | succ {v} : Value v → Value (.succ v)

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
/-
          Value v                              f ⟶ f'                     Value v    a ⟶ a'
  ──────────────────────────────── beta   ────────────────── app1   ──────────────────────── app2
   app (lam A t) v ⟶ t[v]                  app f a ⟶ app f' a       app v a ⟶ app v a'

  ─────────────────────── iteTrue   ─────────────────────── iteFalse         c ⟶ c'
   ite tru t e ⟶ t                   ite fls t e ⟶ e                  ──────────────────────────── ite
                                                                        ite c t e ⟶ ite c' t e
       t ⟶ t'                                               Value v                    t ⟶ t'
  ─────────────────── succ  ───────────────── predZero  ──────────────────── predSucc  ─────────────────── pred
   succ t ⟶ succ t'          pred zero ⟶ zero           pred (succ v) ⟶ v              pred t ⟶ pred t'

                                       Value v                            t ⟶ t'
  ───────────────────── iszeroZero  ───────────────────────── iszeroSucc  ─────────────────────── iszero
   iszero zero ⟶ tru                 iszero (succ v) ⟶ fls               iszero t ⟶ iszero t'

  where t[v] = subst (subst1 v) t.
-/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t'} : Step t t' → Step (.succ t) (.succ t')
  | predZero : Step (.pred .zero) .zero
  | predSucc {v} : Value v → Step (.pred (.succ v)) v
  | pred {t t'} : Step t t' → Step (.pred t) (.pred t')
  | iszeroZero : Step (.iszero .zero) .tru
  | iszeroSucc {v} : Value v → Step (.iszero (.succ v)) .fls
  | iszero {t t'} : Step t t' → Step (.iszero t) (.iszero t')

/-- Executable version of `Value`. -/
def isValue : Term → Bool
  | .lam _ _ => true
  | .tru => true
  | .fls => true
  | .zero => true
  | .succ t => isValue t
  | _ => false

/-- Executable version of `Step`: `none` means "no step possible". -/
def step : Term → Option Term
  | .app f a =>
    if isValue f then
      if isValue a then
        match f with
        | .lam _ t => some (subst (subst1 a) t)
        | _ => none
      else (step a).map (.app f ·)
    else (step f).map (.app · a)
  | .ite c t e =>
    if isValue c then
      match c with
      | .tru => some t
      | .fls => some e
      | _ => none
    else (step c).map (.ite · t e)
  | .succ t => (step t).map .succ
  | .pred t =>
    if isValue t then
      match t with
      | .zero => some .zero
      | .succ v => some v
      | _ => none
    else (step t).map .pred
  | .iszero t =>
    if isValue t then
      match t with
      | .zero => some .tru
      | .succ _ => some .fls
      | _ => none
    else (step t).map .iszero
  | _ => none

/-- Take up to `fuel` steps. -/
def eval : Nat → Term → Term
  | 0, t => t
  | n + 1, t =>
    match step t with
    | some t' => eval n t'
    | none => t

/-! ## Soundness of the interpreter -/

theorem isValue_sound {t : Term} : isValue t = true → Value t := by
  sorry

theorem step_sound {t t' : Term} : step t = some t' → Step t t' := by
  induction t generalizing t' with
  | app f a ihf iha =>
    intro h
    simp only [step] at h
    sorry
  | ite c t e ihc =>
    intro h
    simp only [step] at h
    split at h
    · split at h
      · injection h with h
        rw [← h]
        exact .iteTrue
      · injection h with h
        rw [← h]
        exact .iteFalse
      · contradiction
    · cases hs : step c with
      | none => simp [hs] at h
      | some c' =>
        simp [hs] at h
        rw [← h]
        exact .ite (ihc hs)
  | succ t ih =>
    intro h
    simp only [step] at h
    cases hs : step t with
    | none => simp [hs] at h
    | some t'' =>
      simp [hs] at h
      rw [← h]
      exact .succ (ih hs)
  | pred t ih =>
    intro h
    simp only [step] at h
    split at h
    · next hv =>
      split at h
      · injection h with h
        rw [← h]
        exact .predZero
      · injection h with h
        rw [← h]
        exact .predSucc (isValue_sound hv)
      · contradiction
    · cases hs : step t with
      | none => simp [hs] at h
      | some t'' =>
        simp [hs] at h
        rw [← h]
        exact .pred (ih hs)
  | iszero t ih =>
    intro h
    simp only [step] at h
    split at h
    · next hv =>
      split at h
      · injection h with h
        rw [← h]
        exact .iszeroZero
      · injection h with h
        rw [← h]
        exact .iszeroSucc (isValue_sound hv)
      · contradiction
    · cases hs : step t with
      | none => simp [hs] at h
      | some t'' =>
        simp [hs] at h
        rw [← h]
        exact .iszero (ih hs)
  | _ =>
    intro h
    simp [step] at h

theorem eval_star (n : Nat) (t : Term) : Star Step t (eval n t) := by
  sorry
