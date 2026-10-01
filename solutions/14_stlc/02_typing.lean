/-
# 14.02 — The typing relation

Which type does `.var 0` have? That depends on where it occurs, so the typing
judgement carries a **context** `Γ`, which records the types of the free
variables. With de Bruijn indices a context is just a list:
`Γ[x]?` is the type of `.var x`.

    abbrev Ctx := List Ty

When we go under a binder `lam A t`, the new variable becomes `var 0` and all
the others move up by one, which is exactly what consing does: the body is
checked in `A :: Γ`. For example, `[.nat, .bool]` says that `var 0 : nat` and
`var 1 : bool`.

We write `Γ ⊢ t : T` ("in context Γ, term t has type T") as
`HasType Γ t T`. Here are the inference rules. The `var`, `lam` and `app` rules are
new, and the others are those of chapter 12:

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

Each rule is a constructor of the inductive predicate `HasType` below. A typing
*derivation* is a tree of rule applications, and in Lean it is a term built
from these constructors:

    example : HasType [] (.lam .bool (.var 0)) (.bool ⇒ .bool) :=
      HasType.lam (HasType.var rfl)

Here `rfl` proves `[.bool][0]? = some .bool`. In tactic mode you can build the
same tree with `apply HasType.lam`, `apply HasType.var`, `rfl`, … .

To show that a term has **no** type, assume a derivation and take it apart with
`cases`. Lean knows which rule could have been used last (only `app` builds an
`.app`), and when no rule fits, `cases` closes the goal.

## Your task

Prove the three typing judgements and the two "ill-typed" statements below.
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

def twice : Term := .lam (.nat ⇒ .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0))))

/-! ## Contexts and the typing relation -/

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

example : HasType [] (.lam .bool (.var 0)) (.bool ⇒ .bool) :=
  HasType.lam (HasType.var rfl)

theorem typed_const : HasType [] (.lam .nat (.lam .bool (.var 1))) (.nat ⇒ .bool ⇒ .nat) :=
  HasType.lam (HasType.lam (HasType.var rfl))

theorem typed_open : HasType [.nat, .nat ⇒ .bool] (.app (.var 1) (.succ (.var 0))) .bool := by
  apply HasType.app
  · apply HasType.var
    rfl
  · apply HasType.succ
    apply HasType.var
    rfl

theorem typed_twice : HasType [] twice ((.nat ⇒ .nat) ⇒ .nat ⇒ .nat) :=
  .lam (.lam (.app (.var rfl) (.app (.var rfl) (.var rfl))))

theorem untyped_app : ∀ T, ¬ HasType [] (.app .tru .zero) T := by
  intro T h
  cases h with
  | app hf _ => cases hf

theorem untyped_var : ∀ T, ¬ HasType [] (.var 0) T := by
  intro T h
  cases h with
  | var h => cases h
