/-
# 05.01 — Chaining `Option`s with `do`

Suppose we want the sum of the first elements of two lists. With `head?`
from chapter 02, both lookups may fail, and we have to check each one:

    def addHeads (xs ys : List Nat) : Option Nat :=
      match xs.head? with
      | none   => none
      | some x =>
        match ys.head? with
        | none   => none
        | some y => some (x + y)

This nesting gets ugly fast. The pattern "if it's `none`, stop with `none`;
otherwise continue with the value" is so common that Lean has syntax for it:

    def addHeads (xs ys : List Nat) : Option Nat := do
      let x ← xs.head?        -- stop with `none` if there is no head
      let y ← ys.head?
      pure (x + y)            -- `pure v` is `some v` here

`let x ← e` runs the "computation" `e`, and on success binds its result to
`x`. `pure v` wraps a plain value. This is `do` notation, and `Option` is a
**monad**. Don't worry about that word: for us a monad is just a type like
`Option α` that supports `pure` and `←`. Despite the look, there is no
mutation here; the `do` block is translated into nested `match`es like the
one above.

`xs[i]?` returns the element at index `i` (counting from 0), if any.

## Your task

Use `do` notation in all three functions.

1. `addHeads xs ys` as above (try writing it yourself).
2. `sumFirstTwo xs` returns `xs[0] + xs[1]`, or `none` if `xs` has fewer
   than two elements.
3. `divChain a b c` computes `(a / b) / c` using `safeDiv`, failing if
   either divisor is 0.
-/

def safeDiv (n k : Nat) : Option Nat :=
  if k == 0 then none else some (n / k)

def addHeads (xs ys : List Nat) : Option Nat := do
  let x ← xs.head?
  let y ← ys.head?
  pure (x + y)

def sumFirstTwo (xs : List Nat) : Option Nat := do
  let a ← xs[0]?
  let b ← xs[1]?
  pure (a + b)

def divChain (a b c : Nat) : Option Nat := do
  let q ← safeDiv a b
  safeDiv q c

#eval addHeads [1, 2] [10]
#eval sumFirstTwo [5]
#eval divChain 100 5 2
