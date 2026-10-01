/- HINT
Each proof is a `fun` taking one argument per arrow on the left, e.g.
`fun hp hq => …`. In the body, apply hypotheses like functions.

For `imp_trans`: `fun hpq hqr hp => hqr (…)`.
-/
example {P Q : Prop} : P → Q → P := @const_intro P Q
example {P Q R : Prop} : (P → Q) → (Q → R) → P → R := @imp_trans P Q R
example {P Q : Prop} : (P → P → Q) → P → Q := @imp_dup P Q
