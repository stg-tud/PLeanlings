/- HINT
To prove `Even 6`, `apply Even.ss` until the goal is `Even 0`. To prove a
negation, `intro h` and then take `h` apart with `cases h`.

`Even 3` can only come from rule `ss` with premise `Even 1`; so `cases h`
once, then `cases` again on the premise.
-/
-- The rules of `Even` must stay exactly as given:
example : Even 0 := Even.zero
example {n : Nat} (h : Even n) : Even (n + 2) := Even.ss h
example {n : Nat} (h : Even n) : n = 0 ∨ ∃ m, n = m + 2 ∧ Even m := by
  cases h with
  | zero => exact Or.inl rfl
  | ss h => exact Or.inr ⟨_, rfl, h⟩
example : Even 6 := even_six
example : ¬ Even 1 := not_even_one
example (n : Nat) (h : Even (n + 2)) : Even n := even_inv n h
example : ¬ Even 3 := not_even_three
