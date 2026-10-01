/- HINT
For `last?`, the order of the cases matters: first `[]`, then `[x]`, then
`_ :: xs`.

For `zip`, match on both lists at once. Only the case where *both* lists are
non-empty produces a pair; every other case gives `[]`.
-/
example : {α : Type} → List α → Option α := @last?
example : {α : Type} → Nat → α → List α := @replicate
example : {α β : Type} → List α → List β → List (α × β) := @zip
#guard last? [1, 2, 3] = some 3
#guard last? ([] : List Nat) = none
#guard last? ["only"] = some "only"
#guard replicate 3 "la" = ["la", "la", "la"]
#guard replicate 0 'x' = []
#guard replicate 1 true = [true]
#guard zip [1, 2, 3] ["a", "b"] = [(1, "a"), (2, "b")]
#guard zip ['a'] [1, 2, 3] = [('a', 1)]
#guard zip ([] : List Nat) [1, 2] = []
#guard zip [1, 2] [3, 4] = [(1, 3), (2, 4)]
