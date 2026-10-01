/-
# 11.07 — An executable step function

`Step` is a *relation*: it says which steps are allowed, but it is not a
program we can run. An implementation would rather have a *function*

    step : Term → Option Term

returning the next term, or `none` if `t` is a normal form. Since `Step` is
deterministic (11.04), such a function can exist. Below it is written by
pattern matching, one line per rule. The test `isNumVal` decides the side
condition `NValue v`. Iterating `step` gives an interpreter, `run`.

Now we have two definitions of the same thing, and we prove that they
agree. **Soundness** says the function only takes steps the relation
allows:

    step t = some t'   →   t ⟶ t'

## A new tactic: `fun_induction`

`step` has overlapping patterns and nested recursion, so a plain
`induction t` produces awkward goals. Lean derives a custom induction
principle from the definition of a recursive function, following its
pattern matching *exactly*: one case per line of `step`, each with an
induction hypothesis for every recursive call on that line and with
`step` already unfolded. `fun_induction step t` uses it.

For example, for the line `| .succ t => (step t).map .succ` you get the case

    t  : Term
    ih : ∀ t', step t = some t' → Step t t'
    ⊢ ∀ t', Option.map Term.succ (step t) = some t' → Step (.succ t) t'

After `intro t' h`, `simp at h` turns `h` into
`∃ a, step t = some a ∧ Term.succ a = t'`, which you can take apart with
`obtain ⟨a, ha, rfl⟩ := h`.

The cases are named `case1`, `case2`, … in the order of the lines of `step`.

## Your task

1. Prove `isNumVal_sound`.
2. Fill in the missing cases of `step_sound`.
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

/-- Decide whether a term is a numeric value. -/
def Term.isNumVal : Term → Bool
  | .zero => true
  | .succ t => t.isNumVal
  | _ => false

def step : Term → Option Term
  | .ite .tru t _ => some t                                              -- case1
  | .ite .fls _ e => some e                                              -- case2
  | .ite c t e => (step c).map (fun c' => .ite c' t e)                   -- case3
  | .succ t => (step t).map .succ                                        -- case4
  | .pred .zero => some .zero                                            -- case5
  | .pred (.succ v) =>
      if v.isNumVal then some v                                          -- case6
      else (step v).map (fun v' => .pred (.succ v'))                     -- case7
  | .pred t => (step t).map .pred                                        -- case8
  | .iszero .zero => some .tru                                           -- case9
  | .iszero (.succ v) =>
      if v.isNumVal then some .fls                                       -- case10
      else (step v).map (fun v' => .iszero (.succ v'))                   -- case11
  | .iszero t => (step t).map .iszero                                    -- case12
  | _ => none                                                            -- case13

/-- Run for at most `fuel` steps. -/
def run : Nat → Term → Term
  | 0, t => t
  | fuel + 1, t =>
    match step t with
    | some t' => run fuel t'
    | none => t

-- if iszero (pred (succ 0)) then succ 0 else 0   ⟶*   succ 0
#eval run 100 (.ite (.iszero (.pred (.succ .zero))) (.succ .zero) .zero)
-- succ (pred true) gets stuck
#eval run 100 (.succ (.pred .tru))

/-! ## Exercises -/

theorem isNumVal_sound {t : Term} (h : t.isNumVal = true) : NValue t := by
  sorry

theorem step_sound (t : Term) : ∀ t', step t = some t' → Step t t' := by
  fun_induction step t with
  | case1 => intro t' h; cases h; exact Step.iteTrue
  | case2 => intro t' h; cases h; exact Step.iteFalse
  | case3 c t e _ _ ih =>
    sorry
  | case4 t ih =>
    intro t' h
    simp at h
    obtain ⟨t'', ht, rfl⟩ := h
    exact Step.succ (ih t'' ht)
  | case5 => intro t' h; cases h; exact Step.predZero
  | case6 v hv =>
    sorry
  | case7 v _ ih =>
    intro t' h
    simp at h
    obtain ⟨v', hv, rfl⟩ := h
    exact Step.pred (Step.succ (ih v' hv))
  | case8 t _ _ ih =>
    intro t' h
    simp at h
    obtain ⟨t'', ht, rfl⟩ := h
    exact Step.pred (ih t'' ht)
  | case9 => intro t' h; cases h; exact Step.iszeroZero
  | case10 v hv =>
    sorry
  | case11 v _ ih =>
    intro t' h
    simp at h
    obtain ⟨v', hv, rfl⟩ := h
    exact Step.iszero (Step.succ (ih v' hv))
  | case12 t _ _ ih =>
    sorry
  | case13 => intro t' h; cases h
