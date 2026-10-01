/- HINT
`succ` works exactly like the given `pred` case. For `iszero`, the premise
type is the same but the result is `some .bool`.

For `ite`, match on all three subterm types at once; in the case
`| some .bool, some T, some E =>` return
`if T = E then some T else none`.
-/
#guard typeOf .tru == some .bool
#guard typeOf .zero == some .nat
#guard typeOf (.succ .zero) == some .nat
#guard typeOf (.succ .tru) == none
#guard typeOf (.iszero (.pred .zero)) == some .bool
#guard typeOf (.iszero .fls) == none
#guard typeOf (.ite (.iszero .zero) (.succ .zero) .zero) == some .nat
#guard typeOf (.ite .tru .fls .tru) == some .bool
#guard typeOf (.ite .tru .zero .fls) == none
#guard typeOf (.ite .zero .zero .zero) == none
#guard typeOf (.ite .tru (.succ .fls) (.succ .fls)) == none
#guard typeOf (.pred (.ite .fls .zero (.succ .zero))) == some .nat
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
