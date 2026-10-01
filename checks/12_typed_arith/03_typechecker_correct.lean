/- HINT
Soundness: in each missing case do `intro T h` and `cases h` (this turns
`h : some E = some T` into `T := E`). Then build the derivation from the
induction hypotheses, e.g. `ihc _ hc : HasType c .bool`. Compare with the
given `case9`.

Completeness: `induction h with`, one case per typing rule. The axioms are
`rfl`; for the others try `simp [typeOf, ih]` (with all induction
hypotheses in the `ite` case).
-/
example : ∀ t T, typeOf t = some T → HasType t T := typeOf_sound
example : ∀ {t : Term} {T : Ty}, HasType t T → typeOf t = some T := @typeOf_complete
example : typeOf (.ite (.iszero .zero) (.succ .zero) .zero) = some .nat := rfl
example : typeOf (.ite .tru .zero .fls) = none := rfl
example : typeOf (.iszero .fls) = none := rfl
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
