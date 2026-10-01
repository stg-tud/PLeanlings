/- HINT
`count` compares elements with `==`, so it needs the same `[BEq α]` argument
as `contains`.

In `showAll`, `toString x` converts one element. The `[x]` case has no
comma; the `x :: xs` case puts `", "` between `toString x` and the rest.
-/
example : {α : Type} → [BEq α] → α → List α → Nat := @count
example : {α : Type} → [ToString α] → List α → String := @showAll
#guard count 1 [1, 2, 1, 3] = 2
#guard count 5 [1, 2, 3] = 0
#guard count "a" ["a", "a", "a"] = 3
#guard count 'x' [] = 0
#guard showAll [1, 2, 3] = "1, 2, 3"
#guard showAll [true, false] = "true, false"
#guard showAll ([] : List Nat) = ""
#guard showAll [42] = "42"
#guard showAll ["a", "b"] = "a, b"
