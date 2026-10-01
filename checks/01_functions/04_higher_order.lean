/- HINT
`twice f x` is literally `f (f x)`.

`compose g f` must return a function, so write `fun x => …` and apply
first `f`, then `g`. For `fourTimes`: applying `f` four times is applying
"`f` twice" twice.
-/
example : (Nat → Nat) → Nat → Nat := twice
example : (Nat → Nat) → (Nat → Nat) → Nat → Nat := compose
example : (Nat → Nat) → Nat → Nat := fourTimes
example : twice (· + 3) 10 = 16 := rfl
example : twice (· * 2) 5 = 20 := rfl
example : twice (fun x => x * x) 3 = 81 := rfl
example : compose (· * 2) (· + 1) 5 = 12 := rfl
example : compose (· + 1) (· * 2) 5 = 11 := rfl
example : compose (· - 3) (· * 10) 1 = 7 := rfl
example : fourTimes (· * 2) 1 = 16 := rfl
example : fourTimes (· + 1) 0 = 4 := rfl
example : fourTimes (· * 3) 1 = 81 := rfl
