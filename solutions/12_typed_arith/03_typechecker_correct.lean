/-
# 12.03 — The type checker is correct

We have a specification (`HasType`) and an implementation (`typeOf`).
They agree:

* **Soundness**: if the checker says `T`, there is a typing derivation.

      typeOf t = some T   →   ⊢ t : T

* **Completeness**: if there is a typing derivation, the checker finds it.

      ⊢ t : T   →   typeOf t = some T

(Together: `typeOf t = some T ↔ HasType t T`.)

**Completeness** is a rule induction on `⊢ t : T`. In each case the
induction hypotheses tell you what `typeOf` returns for the subterms, and
`simp [typeOf, ih]` computes the rest.

**Soundness** follows the structure of the *function*, so we use
`fun_induction typeOf t` (introduced in 11.07). It gives one case per
match line of `typeOf`, in order, each with facts about the
recursive calls, such as `hc : typeOf c = some Ty.bool`. The cases where
`typeOf` returns `none` are trivial (`h : none = some T`). The binder
names for the interesting cases are given below; in the `ite` case, Lean
has already used the `if T = E` test to identify the two branch types.

## Your task

Prove both directions.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Term where
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving Repr, DecidableEq

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

def typeOf : Term → Option Ty
  | .tru => some .bool
  | .fls => some .bool
  | .ite c t e =>
    match typeOf c, typeOf t, typeOf e with
    | some .bool, some T, some E => if T = E then some T else none
    | _, _, _ => none
  | .zero => some .nat
  | .succ t =>
    match typeOf t with
    | some .nat => some .nat
    | _ => none
  | .pred t =>
    match typeOf t with
    | some .nat => some .nat
    | _ => none
  | .iszero t =>
    match typeOf t with
    | some .nat => some .bool
    | _ => none

/-! ## Exercises -/

theorem typeOf_sound (t : Term) : ∀ T, typeOf t = some T → HasType t T := by
  fun_induction typeOf t with
  | case1 => intro T h; cases h; exact HasType.tru
  | case2 => intro T h; cases h; exact HasType.fls
  | case3 c t e E he hc ht ihc iht ihe =>
    -- he : typeOf e = some E,  hc : typeOf c = some .bool,  ht : typeOf t = some E
    intro T h
    cases h
    exact HasType.ite (ihc _ hc) (iht _ ht) (ihe _ he)
  | case4 => intro T h; cases h
  | case5 => intro T h; cases h
  | case6 => intro T h; cases h; exact HasType.zero
  | case7 t ht ih =>
    intro T h
    cases h
    exact HasType.succ (ih _ ht)
  | case8 => intro T h; cases h
  | case9 t ht ih =>
    intro T h
    cases h
    exact HasType.pred (ih _ ht)
  | case10 => intro T h; cases h
  | case11 t ht ih =>
    intro T h
    cases h
    exact HasType.iszero (ih _ ht)
  | case12 => intro T h; cases h

theorem typeOf_complete {t : Term} {T : Ty} (h : HasType t T) : typeOf t = some T := by
  induction h with
  | tru => rfl
  | fls => rfl
  | zero => rfl
  | ite _ _ _ ihc iht ihe => simp [typeOf, ihc, iht, ihe]
  | succ _ ih => simp [typeOf, ih]
  | pred _ ih => simp [typeOf, ih]
  | iszero _ ih => simp [typeOf, ih]

theorem typeOf_iff (t : Term) (T : Ty) : typeOf t = some T ↔ HasType t T :=
  ⟨typeOf_sound t T, typeOf_complete⟩
