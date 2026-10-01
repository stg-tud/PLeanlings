/- HINT
`le_three_five`: `apply Le.step` until the two numbers agree. `le_zero` is an
ordinary induction on `n`. The other two are rule inductions with
`induction h with | refl => … | step h ih => …`.

For `le_trans` do the induction on `hbc`, not `hab`. For `le_sound`, `omega`
closes both cases (using `ih`).
-/
-- The rules of `Le` must stay exactly as given:
example (n : Nat) : Le n n := Le.refl n
example {n m : Nat} (h : Le n m) : Le n (m + 1) := Le.step h
example {n m : Nat} (h : Le n m) : n = m ∨ ∃ k, m = k + 1 ∧ Le n k := by
  cases h with
  | refl => exact Or.inl rfl
  | step h => exact Or.inr ⟨_, rfl, h⟩
example : Le 3 5 := le_three_five
example : ∀ n, Le 0 n := le_zero
example {a b c : Nat} : Le a b → Le b c → Le a c := le_trans
example {n m : Nat} : Le n m → n ≤ m := le_sound
