/-
# 04.02 — Polymorphic lists

Lean's `List α` is a linked list with elements of any type `α`:

    inductive List (α : Type) where
      | nil  : List α
      | cons (head : α) (tail : List α) : List α

with the notation `[]` for `nil`, `x :: xs` for `cons x xs`, and
`[1, 2, 3]` for `1 :: 2 :: 3 :: []`. `List` itself is a function from types
to types: `List Nat`, `List String`, `List (List Bool)`, …

Generic functions take the element type as an implicit argument:

    def myLength {α : Type} : List α → Nat
      | []      => 0
      | _ :: xs => myLength xs + 1

The library already has most list functions (`xs.length`, `xs ++ ys`,
`xs.reverse`, …), but writing them yourself is good practice.

## Your task

1. `last? xs` returns the last element of `xs`, or `none` if `xs` is empty.
   (Hint: you may match on `[x]`, the list with exactly one element.)
2. `replicate n x` is the list containing `n` copies of `x`.
3. `zip xs ys` pairs up corresponding elements, stopping when either list
   ends: `zip [1, 2, 3] ["a", "b"] = [(1, "a"), (2, "b")]`.
-/

def myLength {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => myLength xs + 1

def last? {α : Type} : List α → Option α
  | []      => sorry
  | [x]     => sorry
  | _ :: xs => sorry

def replicate {α : Type} (n : Nat) (x : α) : List α :=
  sorry

def zip {α β : Type} : List α → List β → List (α × β) := sorry
