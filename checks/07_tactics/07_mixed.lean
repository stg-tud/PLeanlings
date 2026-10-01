/- HINT
`omega` does not know `step`: `unfold step` (or `unfold step at h`) first.
For the `∃`, pick a witness that is one larger than `n`.

`step_exists`: `exists n + 1`, then `constructor`; the first part is
`simp [step]`, the second `omega`.
-/
example : step 5 = 4 := rfl
example : step 0 = 0 := rfl
example (n : Nat) (h : 0 < n) : step n < n := step_lt n h
example (n : Nat) : ∃ m, step m = n ∧ n < m := step_exists n
example (n : Nat) : step n = 0 ∨ step n + 1 = n := step_cases n
example (n : Nat) (h : step n = n) (hn : n ≠ 0) : False := no_fixpoint n h hn
