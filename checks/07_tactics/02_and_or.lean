/- HINT
To use a hypothesis, take it apart first (`cases`, `obtain`, `rcases`).
Then build the goal with `constructor`, `left`, `right` and `exact`.

`rcases h with ⟨hp, hq⟩ | ⟨hp, hr⟩` splits `(P ∧ Q) ∨ (P ∧ R)` in one go.
You may also write `exact ⟨hp, Or.inl hq⟩` to build a term directly.
-/
example {P Q : Prop} (h : P ∨ Q) : Q ∨ P := or_swap h
example {P Q R : Prop} (h : (P ∧ Q) ∨ (P ∧ R)) : P ∧ (Q ∨ R) := or_and_distrib h
example {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := @and_assoc' P Q R
