/- HINT
Both functions have a case for `[]` and a case for `x :: xs` with a
recursive call on `xs`. In `filter`, use `if p x then … else …`.

For `squaresOfEvens`: first filter, then map.
-/
example : {α β : Type} → (α → β) → List α → List β := @map
example : {α : Type} → (α → Bool) → List α → List α := @filter
example : List Nat → List Nat := squaresOfEvens
#guard map (· * 2) [1, 2, 3] = [2, 4, 6]
#guard map toString [1, 2] = ["1", "2"]
#guard map (· + 1) [] = []
#guard filter (· > 1) [1, 2, 3] = [2, 3]
#guard filter (· > 5) [1, 2, 3] = []
#guard filter (fun _ => true) [3, 1, 2] = [3, 1, 2]
#guard filter (· % 2 == 1) [1, 2, 3, 4, 5] = [1, 3, 5]
#guard squaresOfEvens [1, 2, 3, 4, 5, 6] = [4, 16, 36]
#guard squaresOfEvens [] = []
#guard squaresOfEvens [1, 3] = []
#guard squaresOfEvens [0, 10] = [0, 100]
