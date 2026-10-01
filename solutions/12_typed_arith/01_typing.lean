/-
# 12.01 — Types

In chapter 11 we met **stuck terms** like `succ true` or
`if 0 then true else false`: normal forms that are not values, i.e.
run-time errors. We would like to reject such programs *before* running
them. That is what a **type system** does.

Our language has two types:

    T ::= Bool | Nat

and the **typing relation** `⊢ t : T` ("`t` has type `T`") is defined by
inference rules, one per syntactic form:

    ─────────────── tru     ─────────────── fls     ────────────── zero
    ⊢ true : Bool           ⊢ false : Bool          ⊢ 0 : Nat

    ⊢ c : Bool    ⊢ t : T    ⊢ e : T
    ───────────────────────────────── ite
       ⊢ if c then t else e : T

      ⊢ t : Nat                ⊢ t : Nat                 ⊢ t : Nat
    ───────────────── succ   ───────────────── pred   ──────────────────── iszero
    ⊢ succ t : Nat           ⊢ pred t : Nat           ⊢ iszero t : Bool

Read the `ite` rule carefully: the condition must be a `Bool`, and *both*
branches must have the *same* type `T`, which is then the type of the whole
`if`. We do not know in advance which branch will be taken, so we demand
that both are fine.

In Lean, `HasType t T` is an inductive predicate, just like `Step`.

## Types are conservative

A type system is a *static* approximation of run-time behaviour, so it
must sometimes reject programs that would actually run fine. For example

    if true then 0 else false

steps to the value `0`, but it has no type, since the branches have
different types. That is the price of deciding things without running the
program. (Can you see why no type checker can be both safe and accept
*every* program that does not get stuck? Hint: the halting problem.)

## Your task

1. Give typing derivations for the two well-typed terms.
2. Prove that `succ true` has no type at all (compare with 11.03).
3. Prove both halves of the "conservative" example.
-/

/-! ## Given — do not edit -/

inductive Term where
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving Repr, DecidableEq

inductive NValue : Term → Prop
  | zero : NValue .zero
  | succ {v : Term} : NValue v → NValue (.succ v)

inductive Value : Term → Prop
  | tru : Value .tru
  | fls : Value .fls
  | nv {v : Term} : NValue v → Value v

inductive Step : Term → Term → Prop
  | iteTrue {t e : Term} : Step (.ite .tru t e) t
  | iteFalse {t e : Term} : Step (.ite .fls t e) e
  | ite {c c' t e : Term} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t' : Term} : Step t t' → Step (.succ t) (.succ t')
  | predZero : Step (.pred .zero) .zero
  | predSucc {v : Term} : NValue v → Step (.pred (.succ v)) v
  | pred {t t' : Term} : Step t t' → Step (.pred t) (.pred t')
  | iszeroZero : Step (.iszero .zero) .tru
  | iszeroSucc {v : Term} : NValue v → Step (.iszero (.succ v)) .fls
  | iszero {t t' : Term} : Step t t' → Step (.iszero t) (.iszero t')

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

inductive Ty where
  | bool
  | nat
  deriving Repr, DecidableEq

/-

    ─────────────── tru     ─────────────── fls     ────────────── zero
    ⊢ true : Bool           ⊢ false : Bool          ⊢ 0 : Nat

    ⊢ c : Bool    ⊢ t : T    ⊢ e : T
    ───────────────────────────────── ite
       ⊢ if c then t else e : T

      ⊢ t : Nat                ⊢ t : Nat                 ⊢ t : Nat
    ───────────────── succ   ───────────────── pred   ──────────────────── iszero
    ⊢ succ t : Nat           ⊢ pred t : Nat           ⊢ iszero t : Bool
-/
inductive HasType : Term → Ty → Prop
  | tru : HasType .tru .bool
  | fls : HasType .fls .bool
  | ite {c t e : Term} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
  | zero : HasType .zero .nat
  | succ {t : Term} : HasType t .nat → HasType (.succ t) .nat
  | pred {t : Term} : HasType t .nat → HasType (.pred t) .nat
  | iszero {t : Term} : HasType t .nat → HasType (.iszero t) .bool

/-! ## Exercises -/

-- ⊢ if iszero 0 then succ 0 else 0 : Nat
theorem typed1 : HasType (.ite (.iszero .zero) (.succ .zero) .zero) .nat :=
  HasType.ite (HasType.iszero HasType.zero) (HasType.succ HasType.zero) HasType.zero

-- ⊢ iszero (pred (succ 0)) : Bool
theorem typed2 : HasType (.iszero (.pred (.succ .zero))) .bool :=
  HasType.iszero (HasType.pred (HasType.succ HasType.zero))

theorem succ_tru_untyped (T : Ty) : ¬ HasType (.succ .tru) T := by
  intro h
  cases h with
  | succ h' => cases h'

/-- `if true then 0 else false` runs fine, … -/
theorem conservative_runs : Star Step (.ite .tru .zero .fls) .zero :=
  Star.step Step.iteTrue (Star.refl _)

/-- … but has no type. -/
theorem conservative_untyped (T : Ty) : ¬ HasType (.ite .tru .zero .fls) T := by
  intro h
  cases h with
  | ite _ h₁ h₂ =>
    cases h₁
    cases h₂
