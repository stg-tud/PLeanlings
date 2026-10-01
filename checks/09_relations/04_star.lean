/- HINT
`Star.single`: one `step`, then `refl`. `Star.trans`: `induction h1 with
| refl => … | step hab hbc ih => …`. Look at the type of `ih`: Lean has
generalized `h2` for you, so `ih` takes a `Star R _ c` as an argument.

`Star.tail` needs no induction: combine `Star.trans` and `Star.single`.
For `five_to_two`, `apply Star.step (Dec.dec 4)` makes the first step.
-/
-- The rules of `Star` must stay exactly as given:
example {α : Type} {R : α → α → Prop} (a : α) : Star R a a := Star.refl a
example {α : Type} {R : α → α → Prop} {a b c : α} (h1 : R a b) (h2 : Star R b c) :
    Star R a c := Star.step h1 h2
example {α : Type} {R : α → α → Prop} {a c : α} (h : Star R a c) :
    a = c ∨ ∃ b, R a b ∧ Star R b c := by
  cases h with
  | refl => exact Or.inl rfl
  | step h1 h2 => exact Or.inr ⟨_, h1, h2⟩
example (n : Nat) : Dec (n + 1) n := Dec.dec n
example {a b : Nat} (h : Dec a b) : a = b + 1 := by
  cases h with
  | dec => rfl
example {α : Type} {R : α → α → Prop} {a b : α} : R a b → Star R a b := Star.single
example {α : Type} {R : α → α → Prop} {a b c : α} :
    Star R a b → Star R b c → Star R a c := Star.trans
example {α : Type} {R : α → α → Prop} {a b c : α} :
    Star R a b → R b c → Star R a c := Star.tail
example : Star Dec 5 2 := five_to_two
