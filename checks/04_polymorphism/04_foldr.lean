/- HINT
`foldr` on `x :: xs` combines `x` with the folded tail: `f x (foldr f init xs)`.

For the others, think: what is the result for `[]` (that is `init`), and
how do you combine one element with the result for the rest? For `all`
that is `fun x acc => …`.
-/
example : {α β : Type} → (α → β → β) → β → List α → β := @foldr
example : List Nat → Nat := sum
example : {α : Type} → (α → Bool) → List α → Bool := @all
example : {α : Type} → List (List α) → List α := @concat
#guard foldr (fun x acc => s!"({x} {acc})") "nil" [1, 2, 3] = "(1 (2 (3 nil)))"
#guard foldr (· :: ·) [] [1, 2, 3] = [1, 2, 3]
#guard foldr (fun x acc => acc ++ [x]) [] [1, 2, 3] = [3, 2, 1]
#guard sum [1, 2, 3, 4] = 10
#guard sum [] = 0
#guard all (· > 0) [1, 2, 3] = true
#guard all (· > 1) [1, 2, 3] = false
#guard all (· > 1) [2, 3, 0] = false
#guard all (· > 100) [] = true
#guard concat [[1], [2, 3], []] = [1, 2, 3]
#guard concat ([] : List (List Nat)) = []
#guard concat [["a"], [], ["b", "c"]] = ["a", "b", "c"]
-- no explicit recursion: unfolding the definitions once reaches `foldr`
example : ∀ xs, sum xs = foldr (· + ·) 0 xs := fun _ => rfl
