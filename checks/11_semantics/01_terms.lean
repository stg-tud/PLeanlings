/- HINT
`Term.ofNat (n + 1)` is the successor of `Term.ofNat n`. The proof
`nvalue_ofNat` goes by `induction n`; in each case one `NValue` rule applies.

For `succ_tru_not_value`: after `intro h`, `cases h` leaves only the `nv`
rule (the others do not fit `succ tru`). Its premise is `NValue (succ tru)`;
do `cases` on that, too, and once more on the resulting `NValue tru`, for
which no rule fits at all.
-/
example : Term.ofNat 0 = .zero := rfl
example : Term.ofNat 3 = .succ (.succ (.succ .zero)) := rfl
example : ∀ n, NValue (Term.ofNat n) := nvalue_ofNat
example : Value (.succ (.succ .zero)) := value_two
example : ¬ Value (.succ .tru) := succ_tru_not_value
example : Value .tru := Value.tru
example : Value .fls := Value.fls
example : NValue .zero := NValue.zero
example : NValue (.succ .zero) := NValue.succ NValue.zero
example : Value .zero := Value.nv NValue.zero
example : ∀ t, NValue t → NValue (.succ t) := fun _ h => NValue.succ h
