/-
# 11.02 — Small-step operational semantics

The interpreter of chapter 10 computed the meaning of a program in one go.
An **operational semantics** instead describes *how* a program runs, one
small computation step at a time. We write `t ⟶ t'` ("`t` steps to
`t'`") and define the relation by inference rules:

**Computation rules** (where the actual work happens):

    ─────────────────────────── iteTrue    ──────────────────────────── iteFalse
    if true then t else e ⟶ t              if false then t else e ⟶ e

    ─────────── predZero          NValue v
    pred 0 ⟶ 0               ─────────────────── predSucc
                              pred (succ v) ⟶ v

    ──────────────── iszeroZero        NValue v
    iszero 0 ⟶ true              ──────────────────────── iszeroSucc
                                  iszero (succ v) ⟶ false

**Congruence rules** (where to look for the next step):

                  c ⟶ c'                                t ⟶ t'
    ──────────────────────────────────────── ite    ───────────────── succ
    if c then t else e ⟶ if c' then t else e        succ t ⟶ succ t'

          t ⟶ t'                       t ⟶ t'
    ───────────────── pred    ───────────────────── iszero
    pred t ⟶ pred t'          iszero t ⟶ iszero t'

The congruence rules fix an **evaluation order**: in `if c then t else e`
we only ever step inside the condition `c`, never inside the branches. And
`predSucc` only fires once the argument is fully evaluated (`NValue v`).

In Lean, each rule becomes a constructor of an inductive predicate `Step`,
just like the inference-rule definitions of chapter 08. A *derivation* of
`t ⟶ t'` is then a term built from constructors, e.g.

    -- iszero (pred 0) ⟶ iszero 0
    example : Step (.iszero (.pred .zero)) (.iszero .zero) :=
      Step.iszero Step.predZero

A *run* of a program is a sequence of steps: the reflexive–transitive
closure `Star Step` from chapter 09.

## Your task

Prove the single steps and the multi-step run below. For each single step,
first figure out which rule is used at the *root* of the derivation.
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

/-! ## Exercises -/

-- if (iszero 0) then 0 else (succ 0)   ⟶   if true then 0 else (succ 0)
theorem step1 :
    Step (.ite (.iszero .zero) .zero (.succ .zero)) (.ite .tru .zero (.succ .zero)) :=
  sorry

-- pred (succ (succ 0))   ⟶   succ 0
theorem step2 : Step (.pred (.succ (.succ .zero))) (.succ .zero) :=
  sorry

-- succ (pred (succ 0))   ⟶   succ 0
theorem step3 : Step (.succ (.pred (.succ .zero))) (.succ .zero) :=
  sorry

-- if (iszero (pred (succ 0))) then true else false   ⟶*   true
-- (three steps: write down the intermediate terms first!)
theorem run1 : Star Step (.ite (.iszero (.pred (.succ .zero))) .tru .fls) .tru := by
  sorry
