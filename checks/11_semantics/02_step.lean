/- HINT
`step1`: the root is a congruence rule, `Step.ite`, whose premise is a step
of the condition `iszero 0 ⟶ true`.
`step2`: `Step.predSucc` needs a proof that `succ 0` is a numeric value.

For `run1`, the three intermediate terms are
`if iszero 0 then …`, `if true then …` and finally `true`.
Use `apply Star.step (…a Step…)` once per step and finish with
`exact Star.refl _`.
-/
example : Step (.ite (.iszero .zero) .zero (.succ .zero)) (.ite .tru .zero (.succ .zero)) := step1
example : Step (.pred (.succ (.succ .zero))) (.succ .zero) := step2
example : Step (.succ (.pred (.succ .zero))) (.succ .zero) := step3
example : Star Step (.ite (.iszero (.pred (.succ .zero))) .tru .fls) .tru := run1
-- the rules of `Step` must be unchanged
example : Step (.ite .tru .zero .fls) .zero := Step.iteTrue
example : Step (.ite .fls .zero .fls) .fls := Step.iteFalse
example (c c' t e : Term) (h : Step c c') : Step (.ite c t e) (.ite c' t e) := Step.ite h
example (t t' : Term) (h : Step t t') : Step (.succ t) (.succ t') := Step.succ h
example : Step (.pred .zero) .zero := Step.predZero
example (v : Term) (h : NValue v) : Step (.pred (.succ v)) v := Step.predSucc h
example (t t' : Term) (h : Step t t') : Step (.pred t) (.pred t') := Step.pred h
example : Step (.iszero .zero) .tru := Step.iszeroZero
example (v : Term) (h : NValue v) : Step (.iszero (.succ v)) .fls := Step.iszeroSucc h
example (t t' : Term) (h : Step t t') : Step (.iszero t) (.iszero t') := Step.iszero h
example : ∀ t, ¬ Step .tru t := fun _ h => nomatch h
example : ∀ t, ¬ Step .zero t := fun _ h => nomatch h
example : ∀ t, ¬ Step (.succ .tru) t := fun _ h => by cases h with | succ h => cases h
example : ¬ Star Step .tru .fls := fun h => by cases h with | step h _ => cases h
