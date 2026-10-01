/-
# 11.03 — Values, normal forms and stuck terms

A term is in **normal form** if no rule applies to it:

    NormalForm t  :=  ∀ t', ¬ (t ⟶ t')

Values are the intended *results* of computation, so they had better be
normal forms: a finished computation should not compute any further. For
our language this is a theorem, proved by case analysis on the value:
`true` and `false` match the conclusion of no rule at all, and for a
numeric value `succ v` only the congruence rule `succ` fits, whose premise
`v ⟶ v'` is impossible by induction.

Is the converse true, is every normal form a value? No! Consider

    succ true

It is not a value (11.01), and no rule applies to it: `succ` needs the
argument to step, but `true` does not step. Such a term is **stuck**: the
program has not finished, but cannot continue either. In a real
implementation this is a *run-time error* ("cannot add 1 to a boolean").
Stuck terms are exactly what a **type system** is meant to rule out; this
is the story of the next chapter.

Proof techniques you need:
* To refute `h : Step .tru t'`, use `cases h`: Lean finds that no rule's
  conclusion matches and closes the goal.
* To prove a statement about all `NValue v`, use `induction` on the
  `NValue` hypothesis, `generalizing` the other term since it changes in
  the induction step.

## Your task

Prove `nvalue_nf`, `value_nf` and `succ_tru_stuck`.
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

inductive NValue : Term → Prop
  | zero : NValue .zero
  | succ {v : Term} : NValue v → NValue (.succ v)

inductive Value : Term → Prop
  | tru : Value .tru
  | fls : Value .fls
  | nv {v : Term} : NValue v → Value v

/-
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
-/
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

/-- No rule applies to `t`. -/
def NormalForm (t : Term) : Prop := ∀ t', ¬ Step t t'

/-! ## Exercises -/

theorem nvalue_nf {v : Term} (hv : NValue v) : NormalForm v := by
  induction hv with
  | zero =>
    sorry
  | succ hv ih =>
    sorry

theorem value_nf {v : Term} (hv : Value v) : NormalForm v := by
  sorry

/-- `succ true` is stuck: a normal form that is not a value. -/
theorem succ_tru_stuck : NormalForm (.succ .tru) ∧ ¬ Value (.succ .tru) := by
  sorry
