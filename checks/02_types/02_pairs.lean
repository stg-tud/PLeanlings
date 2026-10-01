/- HINT
Build a pair with `(_, _)` and take one apart with `.1`/`.2` or a `match`.

For `addPairs`, you can match on two things at once:
`match p, q with | (a, b), (c, d) => …`.
-/
example : Nat × String → String × Nat := swap
example : Nat → Nat → Nat × Nat := divMod
example : Nat × Nat → Nat × Nat → Nat × Nat := addPairs
#guard swap (1, "one") = ("one", 1)
#guard swap (0, "") = ("", 0)
example : divMod 17 5 = (3, 2) := rfl
example : divMod 4 5 = (0, 4) := rfl
example : divMod 20 4 = (5, 0) := rfl
example : addPairs (1, 2) (10, 20) = (11, 22) := rfl
example : addPairs (0, 5) (7, 0) = (7, 5) := rfl
