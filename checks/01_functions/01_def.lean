/- HINT
Look at how `double` is defined and follow the same pattern:
`def square (n : Nat) : Nat := …`.

For `isEven`, `n % 2` is the remainder of dividing by 2. Compare it to `0`
with `==`.
-/
example : Nat → Nat := square
example : Nat → Nat → Nat := sumOfSquares
example : Nat → Bool := isEven
example : square 0 = 0 := rfl
example : square 1 = 1 := rfl
example : square 7 = 49 := rfl
example : square 12 = 144 := rfl
example : sumOfSquares 3 4 = 25 := rfl
example : sumOfSquares 0 5 = 25 := rfl
example : sumOfSquares 2 1 = 5 := rfl
example : isEven 0 = true := rfl
example : isEven 1 = false := rfl
example : isEven 10 = true := rfl
example : isEven 7 = false := rfl
example : isEven 1000 = true := rfl
