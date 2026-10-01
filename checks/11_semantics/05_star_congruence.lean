/- HINT
`Star.lift`: `induction h with | refl => … | step hab _ ih => …`.
In the `step` case you have `hab : R a b` and `ih : Star S (f b) (f c)`;
glue them together with `Star.step` and `hf hab`.

For `star_ite`, the context is `fun c => Term.ite c t e`, so
`Star.lift (fun c => Term.ite c t e) Step.ite h`.
-/
example : ∀ {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β),
    (∀ {a b : α}, R a b → S (f a) (f b)) → ∀ {a b : α}, Star R a b → Star S (f a) (f b) :=
  @Star.lift
example : ∀ {c c' : Term} (t e : Term), Star Step c c' → Star Step (.ite c t e) (.ite c' t e) :=
  @star_ite
example : ∀ {t t' : Term}, Star Step t t' → Star Step (.pred t) (.pred t') := @star_pred
example : ∀ {t t' : Term}, Star Step t t' → Star Step (.iszero t) (.iszero t') := @star_iszero
example : ∀ {t t' : Term}, Star Step t t' → Star Step (.succ t) (.succ t') := @star_succ
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
