/- HINT
For `max3`, you can nest conditionals: `if … then … else if … then … else …`.
Make sure that ties (equal numbers) are handled as well.

For `price`, start with `let cost := 3 * n` and then use `if` on `cost`.
-/
example : Nat → Nat → Nat → Nat := max3
example : Nat → Nat := collatz
example : Nat → Nat := price
example : max3 1 2 3 = 3 := rfl
example : max3 3 2 1 = 3 := rfl
example : max3 2 3 1 = 3 := rfl
example : max3 1 3 2 = 3 := rfl
example : max3 3 1 2 = 3 := rfl
example : max3 2 1 3 = 3 := rfl
example : max3 5 5 1 = 5 := rfl
example : max3 1 5 5 = 5 := rfl
example : max3 5 1 5 = 5 := rfl
example : max3 0 0 0 = 0 := rfl
example : collatz 7 = 22 := rfl
example : collatz 10 = 5 := rfl
example : collatz 0 = 0 := rfl
example : collatz 1 = 4 := rfl
example : price 0 = 0 := rfl
example : price 6 = 18 := rfl
example : price 7 = 16 := rfl
example : price 10 = 25 := rfl
