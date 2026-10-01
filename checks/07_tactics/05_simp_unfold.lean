/- HINT
Tell `simp` which definitions it may unfold: `simp [double]`.
Hypotheses can be passed to `simp` too: `simp [h, double]`.

For `double_show`, write `show n + n = n + n` (the unfolded goal) and then `rfl`.
-/
example : double 3 = 6 := rfl
example : double 0 = 0 := rfl
example : swapPair (1, 2) = (2, 1) := rfl
example (n : Nat) : double (0 + n) = n + n := double_zero_add n
example (p : Nat × Nat) : swapPair (swapPair p) = p := swap_swap p
example (n : Nat) : double n = n + n := double_show n
example (l : List Nat) (h : l = [1, 2]) : l.map double = [2, 4] := map_double l h
