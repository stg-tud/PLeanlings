/- HINT
Start with `cases hv`. For `canonical_bool`, the `tru` and `fls` cases are
`left; rfl` and `right; rfl`. In the `nv hn` case, do `cases hn` as well:
both `HasType .zero .bool` and `HasType (.succ _) .bool` are impossible, so
`cases ht` closes each.

For `canonical_nat`, the `tru`/`fls` cases are impossible (`cases ht`), and
the `nv` case gives you the `NValue` directly.
-/
example : ∀ {v : Term}, Value v → HasType v .bool → v = .tru ∨ v = .fls := @canonical_bool
example : ∀ {v : Term}, Value v → HasType v .nat → NValue v := @canonical_nat
example : ∀ {v : Term}, NValue v → HasType v .nat := @nvalue_nat
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
example : NValue (.succ .zero) := NValue.succ NValue.zero
example : Value .tru ∧ Value .fls ∧ Value .zero := ⟨Value.tru, Value.fls, Value.nv NValue.zero⟩
example : ¬ NValue .tru := fun h => nomatch h
example : ¬ Value (.succ .tru) := fun h => by cases h with | nv h => cases h with | succ h => cases h
