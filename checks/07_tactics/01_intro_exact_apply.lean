/- HINT
Start with `intro` for every arrow in the goal. Then work backwards with
`apply`, and finish with `exact`.

If `apply h` creates two goals, solve them one after the other; the bullet
`·` (typed `\.`) focuses on one goal. For `¬P`, `intro hp` leaves the goal
`False`, and `hnq : Q → False` can be applied to it.
-/
example {P Q R : Prop} : (P → Q → R) → Q → P → R := @swap_args P Q R
example {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (h5 : P 5) : Q 5 := apply_forall h h5
example {P Q : Prop} (hnq : ¬Q) (hpq : P → Q) : ¬P := not_imp_intro hnq hpq
