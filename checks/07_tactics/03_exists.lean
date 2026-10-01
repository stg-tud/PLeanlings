/- HINT
`exists a, b` gives several witnesses at once. To use an existential
hypothesis, first `obtain ⟨w, hw⟩ := h`.

For `exists_and_comm`: `obtain ⟨w, hp, hq⟩ := h`, then `exact ⟨w, hq, hp⟩`.
-/
example : ∃ a b : Nat, a + b = 5 ∧ a = b + 1 := exists_sum
example {P : Nat → Prop} (h : ∀ n, P n) : ∃ n, P n := exists_of_forall h
example {P Q : Nat → Prop} (h : ∃ n, P n ∧ Q n) : ∃ n, Q n ∧ P n := exists_and_comm h
