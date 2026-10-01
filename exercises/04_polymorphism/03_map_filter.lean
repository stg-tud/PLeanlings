/-
# 04.03 — `map` and `filter`

Two of the most useful higher-order functions on lists:

* `map f xs` applies `f` to every element:
  `map (· * 2) [1, 2, 3] = [2, 4, 6]`.
* `filter p xs` keeps only the elements for which `p` returns `true`:
  `filter (· > 1) [1, 2, 3] = [2, 3]`.

They replace most `for` loops you would write in Java or Python. Note how
polymorphic `map` is: `f` may change the element type!

    map toString [1, 2]  =  ["1", "2"]          -- List Nat → List String

The library versions are `List.map` and `List.filter`, usable with dot
notation: `[1, 2, 3].map (· * 2)`.

## Your task

1. Implement `map` (with the type as given).
2. Implement `filter`.
3. Define `squaresOfEvens xs`: the squares of the even elements of `xs`,
   using **your** `map` and `filter`.
-/

def map {α β : Type} (f : α → β) : List α → List β
  | []      => sorry
  | x :: xs => sorry

def filter {α : Type} (p : α → Bool) : List α → List α := sorry

def squaresOfEvens (xs : List Nat) : List Nat :=
  sorry
