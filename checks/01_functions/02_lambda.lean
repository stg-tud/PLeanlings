/- HINT
The type already says what the arguments are, so you only write the body:
`def triple : Nat → Nat := fun x => …`.

`between` takes three arguments: `fun lo hi x => …`. Combine the two
comparisons with `&&`.
-/
example : Nat → Nat := triple
example : Nat → Nat → Nat → Bool := between
example : triple 0 = 0 := rfl
example : triple 1 = 3 := rfl
example : triple 14 = 42 := rfl
example : between 1 10 5 = true := rfl
example : between 1 10 1 = true := rfl
example : between 1 10 10 = true := rfl
example : between 1 10 0 = false := rfl
example : between 1 10 11 = false := rfl
example : between 5 3 4 = false := rfl
