/- HINT
`NormalForm v` unfolds to `∀ t', ¬ Step v t'`, so start each case with
`intro t' h`. Then `cases h`: impossible rules disappear automatically.
In the `succ` case only the congruence rule `Step.succ` remains, and its
premise contradicts the induction hypothesis `ih`.

`value_nf`: `cases hv` and reuse `nvalue_nf` for the `nv` case.
-/
example : ∀ v, NValue v → NormalForm v := @nvalue_nf
example : ∀ v, Value v → NormalForm v := @value_nf
example : NormalForm (.succ .tru) ∧ ¬ Value (.succ .tru) := succ_tru_stuck
example : NormalForm = fun t => ∀ t', ¬ Step t t' := rfl
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
