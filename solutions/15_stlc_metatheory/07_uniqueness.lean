/-
# 15.07 — Uniqueness of types

In our STLC every term has **at most one** type in a given context:

    theorem type_unique : HasType Γ t A → HasType Γ t B → A = B

This holds because the rules are syntax-directed and every `λ` carries its
parameter type. (With unannotated binders, "Curry-style", it would fail:
`λx. x` would have type `bool ⇒ bool` *and* `nat ⇒ nat`.)

**Proof.** Induction on the first derivation, generalizing `B`; then invert
the second derivation with `cases h2`. In the interesting cases:

* `var`: both derivations look up the same variable, so
  `some A = some B`, and `injection` gives `A = B`.
* `lam`: both have the form `A₀ ⇒ _`; the induction hypothesis says the
  result types agree.
* `app`: the induction hypothesis for the function gives `A₁ ⇒ A = A₂ ⇒ B`, and
  `injection` extracts `A = B` (the two argument types are equal too).

## Your task

1. Fill in the `var`, `lam` and `app` cases.
2. Prove the corollary `not_bool_and_nat`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

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

/-! ## Uniqueness -/

theorem type_unique {Γ : Ctx} {t : Term} {A B : Ty} :
    HasType Γ t A → HasType Γ t B → A = B := by
  intro h1 h2
  induction h1 generalizing B with
  | var h =>
    cases h2 with
    | var h' =>
      rw [h] at h'
      injection h'
  | lam _ ih =>
    cases h2 with
    | lam h' => rw [ih h']
  | app _ _ ihf _ =>
    cases h2 with
    | app hf' _ =>
      have h := ihf hf'
      injection h
  | tru => cases h2; rfl
  | fls => cases h2; rfl
  | ite _ _ _ _ iht _ =>
    cases h2 with
    | ite _ ht' _ => exact iht ht'
  | zero => cases h2; rfl
  | succ _ _ => cases h2; rfl
  | pred _ _ => cases h2; rfl
  | iszero _ _ => cases h2; rfl

theorem not_bool_and_nat {Γ : Ctx} {t : Term} :
    HasType Γ t .bool → ¬ HasType Γ t .nat := by
  intro hb hn
  have h := type_unique hb hn
  cases h
