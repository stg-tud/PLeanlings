/- HINT
Unfold `¬ P` in your head to `P → False`: then `¬¬P` is `(P → False) → False`,
and every proof of a negation is a `fun`.

For `not_or_split`, build a pair `⟨fun hp => …, fun hq => …⟩` and use `h`
with `Or.inl hp` / `Or.inr hq`. For `explode`, use `absurd` or `False.elim`.
-/
example {P : Prop} : P → ¬¬P := @double_neg_intro P
example {P Q : Prop} : (P → Q) → ¬Q → ¬P := @contrapositive P Q
example {P Q : Prop} : P → ¬P → Q := @explode P Q
example {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q := @not_or_split P Q
