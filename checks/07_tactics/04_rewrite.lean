/- HINT
Look at the goal and find a subterm that matches the left side of one of
your equations; `rw` with it. Use `← h` to go from right to left, and
`at h` to rewrite a hypothesis.

For `rw_at`: `rw [h2] at h1` turns `h1` into `3 + 0 = b`. Then `rw [← h1]`
replaces `b` in the goal, giving `3 + 0 = 3`, which the automatic `rfl` closes.
For `rw_comm`: `Nat.add_comm a b` and then `Nat.mul_comm`.
-/
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := rw_example a b c h1 h2
example (a b : Nat) (f : Nat → Nat) (h : f a = b) (hb : b = 7) : f a = 7 := rw_back a b f h hb
example (a b : Nat) (h1 : a + 0 = b) (h2 : a = 3) : b = 3 := rw_at a b h1 h2
example (a b c : Nat) : (a + b) * c = c * (b + a) := rw_comm a b c
