/- HINT
Build a conjunction with `⟨_, _⟩`, project with `.1` and `.2`.
Use an `Or` with `match h with | Or.inl hp => … | Or.inr hq => …`.

For `and_or_distrib`, match on `h.2` (the `Q ∨ R` part) and use `h.1` in both cases.
-/
example {P Q : Prop} : P ∧ Q → Q ∧ P := @and_swap P Q
example {P Q : Prop} : P ∨ Q → Q ∨ P := @or_swap P Q
example {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := @and_or_distrib P Q R
