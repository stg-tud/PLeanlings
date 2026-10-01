/- HINT
A `∀` proof is a `fun n => …`; an `∃` proof is a pair `⟨witness, proof⟩`.
Use an `∃` hypothesis with `match h with | ⟨w, hw⟩ => …`.

For `exists_big`, any witness above 10 works, and `by decide` proves `10 < 11`.
-/
example : 7 + 0 = 7 := seven_add_zero
example : ∃ n : Nat, 10 < n := exists_big
example {P Q : Nat → Prop} : (∀ n, P n ∧ Q n) → ∀ n, P n := @forall_and_left P Q
example {P Q : Nat → Prop} : (∃ n, P n ∧ Q n) → ∃ n, P n := @exists_weaken P Q
