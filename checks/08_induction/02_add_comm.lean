/- HINT
Do induction on the first argument. In the `zero` case of `add_comm` you need
`add_zero`; in the `succ` case you need `add_succ` and `ih`.

`simp [add, add_succ, ih]` handles the `succ` case of `add_comm`;
`add_assoc` needs only `add` and `ih`.
-/
example (m : Nat) : add 0 m = m := rfl
example (n m : Nat) : add (n + 1) m = add n m + 1 := rfl
example : add 2 3 = 5 := rfl
example : ∀ n m, add n m = add m n := add_comm
example : ∀ a b c, add (add a b) c = add a (add b c) := add_assoc
