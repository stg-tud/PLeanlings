/- HINT
For `even_double`, do ordinary induction on `k`; for the other two do rule
induction: `induction h with | zero => … | ss h ih => …`.

In the `ss` cases, the goal mentions `… + 2`; use `have e : … = … := by omega`
and `rw [e]` to bring it into the form `Even (… + 2)`, then `exact Even.ss ih`.
Name the implicit number with `| @ss k h ih =>`. In `even_exists`, first
`obtain ⟨j, hj⟩ := ih`.
-/
example : Even 0 := Even.zero
example {n : Nat} (h : Even n) : Even (n + 2) := Even.ss h
example {n : Nat} (h : Even n) : n = 0 ∨ ∃ m, n = m + 2 ∧ Even m := by
  cases h with
  | zero => exact Or.inl rfl
  | ss h => exact Or.inr ⟨_, rfl, h⟩
example : ∀ k, Even (2 * k) := even_double
example {n : Nat} : Even n → ∃ k, n = 2 * k := even_exists
example {m n : Nat} : Even m → Even n → Even (m + n) := even_add
