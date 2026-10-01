/- HINT
Start with `induction n with | zero => … | succ n ih => …`. The `zero` case
holds by computation (`rfl`). In the `succ` case, unfold `add` once and use
`ih`.

`simp [add, ih]` solves the `succ` case of both theorems.
-/
-- `add` must stay as given (recursion on the first argument):
example (m : Nat) : add 0 m = m := rfl
example (n m : Nat) : add (n + 1) m = add n m + 1 := rfl
example : add 2 3 = 5 := rfl
example : add 4 0 = 4 := rfl
example : ∀ n, add n 0 = n := add_zero
example : ∀ n m, add n (m + 1) = add n m + 1 := add_succ
