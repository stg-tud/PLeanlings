/-
# 11.04 — Determinism

Our semantics is **deterministic**: every term has at most one next step.

    t ⟶ t₁    t ⟶ t₂
    ──────────────────
         t₁ = t₂

This is not automatic. If we added the rule "you may also step inside the
`then` branch", `if c then t else e` could step in two different ways. It
is the congruence rules and the side conditions `NValue v` that make sure
that for every term, at most one rule fits.

The proof is a classic **rule induction**: induction on the derivation of
`t ⟶ t₁` (generalizing `t₂`), and in each case, `cases` on the derivation
of `t ⟶ t₂`. Most combinations are impossible and are closed by `cases` on
an impossible step. Two kinds of cases need thought:

* *Both derivations use the same congruence rule*, e.g. both are
  `Step.ite`: then the induction hypothesis says the conditions step to
  the same term, and we can rewrite with it.
* *A computation rule against a congruence rule*, e.g. `predSucc` (which
  needs `NValue v`) against `pred` (which needs `succ v ⟶ t'`). This is
  impossible because numeric values do not step: use `nvalue_nf` from
  the previous exercise. Recall that `absurd h hn` proves any goal from
  `h : P` and `hn : ¬ P`.

## Your task

Fill in the missing cases.
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

def NormalForm (t : Term) : Prop := ∀ t', ¬ Step t t'

theorem nvalue_nf {v : Term} (hv : NValue v) : NormalForm v := by
  induction hv with
  | zero => intro t' h; cases h
  | succ hv ih => intro t' h; cases h with | succ h' => exact ih _ h'

/-! ## Exercises -/

theorem step_det {t t₁ t₂ : Term} (h₁ : Step t t₁) (h₂ : Step t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | iteTrue =>
    cases h₂ with
    | iteTrue => rfl
    | ite h => cases h          -- `true` does not step
  | iteFalse =>
    cases h₂ with
    | iteFalse => rfl
    | ite h => cases h
  | ite h ih =>
    cases h₂ with
    | iteTrue => cases h
    | iteFalse => cases h
    | ite h' => rw [ih h']
  | succ h ih =>
    cases h₂ with
    | succ h' => rw [ih h']
  | predZero =>
    cases h₂ with
    | predZero => rfl
    | pred h => cases h
  | predSucc hv =>
    sorry
  | pred h ih =>
    sorry
  | iszeroZero =>
    cases h₂ with
    | iszeroZero => rfl
    | iszero h => cases h
  | iszeroSucc hv =>
    sorry
  | iszero h ih =>
    sorry
