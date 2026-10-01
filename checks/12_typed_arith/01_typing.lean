/- HINT
A typing derivation is built from the root: `typed1` is an `if`, so it
starts with `HasType.ite`, which takes three derivations (condition, then,
else) as arguments.

For the negative results: `intro h` and `cases h`. For
`conservative_untyped` you get `h₁ : HasType .zero T` and
`h₂ : HasType .fls T`. `cases h₁` fixes `T := .nat`, and then
`h₂ : HasType .fls .nat` is impossible.
-/
example : HasType (.ite (.iszero .zero) (.succ .zero) .zero) .nat := typed1
example : HasType (.iszero (.pred (.succ .zero))) .bool := typed2
example : ∀ T, ¬ HasType (.succ .tru) T := succ_tru_untyped
example : Star Step (.ite .tru .zero .fls) .zero := conservative_runs
example : ∀ T, ¬ HasType (.ite .tru .zero .fls) T := conservative_untyped
-- the rules of `HasType` must be unchanged
example : HasType .tru .bool := HasType.tru
example : HasType .fls .bool := HasType.fls
example : HasType .zero .nat := HasType.zero
example (c t e : Term) (T : Ty) (h₁ : HasType c .bool) (h₂ : HasType t T) (h₃ : HasType e T) :
    HasType (.ite c t e) T := HasType.ite h₁ h₂ h₃
example (t : Term) (h : HasType t .nat) : HasType (.succ t) .nat := HasType.succ h
example (t : Term) (h : HasType t .nat) : HasType (.pred t) .nat := HasType.pred h
example (t : Term) (h : HasType t .nat) : HasType (.iszero t) .bool := HasType.iszero h
example : ¬ HasType .tru .nat := fun h => nomatch h
example : ¬ HasType .zero .bool := fun h => nomatch h
example : ∀ T, ¬ HasType (.succ .tru) T := fun _ h => by cases h with | succ h => cases h
example : ∀ T, ¬ HasType (.iszero .fls) T := fun _ h => by cases h with | iszero h => cases h
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
-- `Star` must be unchanged
example : Star Step (.pred .zero) .zero := Star.step Step.predZero (Star.refl _)
example : ¬ Star Step .tru .fls := fun h => by cases h with | step h _ => cases h
