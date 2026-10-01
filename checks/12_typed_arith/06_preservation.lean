/- HINT
Every case starts with `cases ht` (use `cases ht with | ite hc h₁ h₂ => …`
to name the premises). For the congruence rules, the induction hypothesis
`ih` turns the premise about the stepping subterm into one about its
successor, e.g. `HasType.ite (ih hc) h₁ h₂`.

`predSucc`: invert twice, `cases ht with | pred h => cases h with
| succ h' => exact h'`.
-/
example : ∀ {t t' : Term} {T : Ty}, HasType t T → Step t t' → HasType t' T := @preservation
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
