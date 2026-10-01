/- HINT
Each missing case is the mirror image of a given one: `iteTrue` of
`iteFalse`, `predSucc` of `predZero`, `iszeroSucc` of `iszeroZero`. The
only difference is the computation rule used for the last step, which
now needs the hypothesis `hv : NValue v`: `Step.predSucc hv`.

For `succ`, no extra step is needed at all: the congruence lemma
`star_succ` does everything.
-/
example : ∀ {t v : Term}, Eval t v → Star Step t v := @eval_star
-- the rules of `Eval` must be unchanged
example : Eval .zero .zero := Eval.val (Value.nv NValue.zero)
example (c t e v : Term) (h₁ : Eval c .tru) (h₂ : Eval t v) : Eval (.ite c t e) v := Eval.iteTrue h₁ h₂
example (c t e v : Term) (h₁ : Eval c .fls) (h₂ : Eval e v) : Eval (.ite c t e) v := Eval.iteFalse h₁ h₂
example (t v : Term) (h₁ : Eval t v) (h₂ : NValue v) : Eval (.succ t) (.succ v) := Eval.succ h₁ h₂
example (t : Term) (h : Eval t .zero) : Eval (.pred t) .zero := Eval.predZero h
example (t v : Term) (h₁ : Eval t (.succ v)) (h₂ : NValue v) : Eval (.pred t) v := Eval.predSucc h₁ h₂
example (t : Term) (h : Eval t .zero) : Eval (.iszero t) .tru := Eval.iszeroZero h
example (t v : Term) (h₁ : Eval t (.succ v)) (h₂ : NValue v) : Eval (.iszero t) .fls := Eval.iszeroSucc h₁ h₂
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
