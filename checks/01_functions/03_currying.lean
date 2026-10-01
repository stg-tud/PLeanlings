/- HINT
`addTen` takes one number and returns one number, so its type is a single
arrow. `scale` takes two numbers.

`add 10` is already a function waiting for the second argument.
-/
example : Nat → Nat := addTen
example : Nat → Nat → Nat := scale
example : Nat → Nat := scaleBy3
example : addTen 0 = 10 := rfl
example : addTen 5 = 15 := rfl
example : addTen 32 = 42 := rfl
example : scale 2 21 = 42 := rfl
example : scale 0 9 = 0 := rfl
example : scaleBy3 7 = 21 := rfl
example : scaleBy3 0 = 0 := rfl
example : scaleBy3 1 = 3 := rfl
