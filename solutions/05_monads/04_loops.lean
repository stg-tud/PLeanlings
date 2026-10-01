/-
# 05.04 — Loops and state (optional style)

Sometimes an imperative loop is the clearest way to write a function. Lean
allows this inside `do` blocks, with **local mutable variables**:

    def sumList (xs : List Nat) : Nat := Id.run do
      let mut total := 0
      for x in xs do
        total := total + x
      return total

`Id.run do …` runs a `do` block that has no other effects. `let mut`
introduces a variable that may be reassigned with `:=`. This is still a
pure function: Lean translates the loop into a `foldl` behind the scenes.

The monad `StateM σ` threads a *state* of type `σ` through a computation.
`get` reads it and `set` replaces it. A classic use is generating fresh
names, e.g. for variables in a compiler:

    def fresh : StateM Nat Nat := do
      let n ← get
      set (n + 1)
      pure n

    #eval (do let a ← fresh; let b ← fresh; pure (a, b)).run' 0   -- (0, 1)

## Your task

1. `maxList xs` returns the largest element of `xs` (and `0` for `[]`).
   Use a `for` loop.
2. `countIf p xs` counts the elements satisfying `p`. Use a `for` loop.
3. `freshNames k` returns `k` fresh names `"x0"`, `"x1"`, … using `fresh`
   (it starts from the current state, and leaves the counter incremented
   by `k`). `for _ in [0:k] do` repeats the loop body `k` times, and inside
   the loop, `let n ← fresh` gets the next number.
-/

def fresh : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def maxList (xs : List Nat) : Nat := Id.run do
  let mut m := 0
  for x in xs do
    if x > m then
      m := x
  return m

def countIf (p : Nat → Bool) (xs : List Nat) : Nat := Id.run do
  let mut c := 0
  for x in xs do
    if p x then
      c := c + 1
  return c

def freshNames (k : Nat) : StateM Nat (List String) := do
  let mut names := []
  for _ in [0:k] do
    let n ← fresh
    names := names ++ [s!"x{n}"]
  return names

#eval maxList [3, 9, 2]
#eval countIf (· > 2) [1, 2, 3, 4]
#eval (freshNames 3).run 0
