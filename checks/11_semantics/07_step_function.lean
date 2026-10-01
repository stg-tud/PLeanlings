/- HINT
`isNumVal_sound`: induction on `t`. In the `succ` case, `h` is (by
definition) `t.isNumVal = true`, so the induction hypothesis applies. In
all other cases except `zero`, `h : false = true`, which
`simp [Term.isNumVal] at h` refutes. (`| _ => …` handles all remaining
cases at once.)

For `case6`, `hv : v.isNumVal = true` and `h : some v = some t'`;
`cases h` substitutes, and `isNumVal_sound hv` gives the premise of
`Step.predSucc`. `case3` and `case12` work like `case4`.
-/
example : ∀ {t : Term}, t.isNumVal = true → NValue t := @isNumVal_sound
example : ∀ t t', step t = some t' → Step t t' := step_sound
example : step (.pred (.succ (.succ .zero))) = some (.succ .zero) := rfl
example : step (.ite (.iszero .zero) .zero .tru) = some (.ite .tru .zero .tru) := rfl
example : step (.succ .tru) = none := rfl
example : step (.iszero (.succ (.pred .zero))) = some (.iszero (.succ .zero)) := rfl
example : run 100 (.ite (.iszero (.pred (.succ .zero))) (.succ .zero) .zero) = .succ .zero := rfl
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
example : NValue (.succ .zero) := NValue.succ NValue.zero
example : Value .tru ∧ Value .fls ∧ Value .zero := ⟨Value.tru, Value.fls, Value.nv NValue.zero⟩
example : ¬ NValue .tru := fun h => nomatch h
example : ¬ Value (.succ .tru) := fun h => by cases h with | nv h => cases h with | succ h => cases h
