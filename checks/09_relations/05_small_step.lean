/- HINT
Work backwards with `apply` and the rule names, e.g. `apply Step.plus_left`.
For `num_stuck`, `intro h` and `cases h`: no rule concludes `num n ⟶ …`.

For `star_plus_left`, use `induction h with | refl => … | step hs hrest ih => …`
and wrap the first step with `Step.plus_left e₂ hs`. For `eval_example`,
`apply Star.step one_step`, then one `plus_nums` step, then `Star.refl`.
-/
-- The rules must stay exactly as given:
example (n m : Nat) : Step (plus (num n) (num m)) (num (n + m)) := Step.plus_nums n m
example {e₁ e₁' : Expr} (e₂ : Expr) (h : Step e₁ e₁') : Step (plus e₁ e₂) (plus e₁' e₂) :=
  Step.plus_left e₂ h
example (n : Nat) {e₂ e₂' : Expr} (h : Step e₂ e₂') : Step (plus (num n) e₂) (plus (num n) e₂') :=
  Step.plus_right n h
example {e e' : Expr} (h : Step e e') : ∃ a b, e = plus a b := by
  cases h with
  | plus_nums n m => exact ⟨_, _, rfl⟩
  | plus_left e₂ _ => exact ⟨_, _, rfl⟩
  | plus_right n _ => exact ⟨_, _, rfl⟩
example {α : Type} {R : α → α → Prop} {a c : α} (h : Star R a c) :
    a = c ∨ ∃ b, R a b ∧ Star R b c := by
  cases h with
  | refl => exact Or.inl rfl
  | step h1 h2 => exact Or.inr ⟨_, h1, h2⟩
example : Step (plus (plus (num 1) (num 2)) (num 3)) (plus (num 3) (num 3)) := one_step
example : ∀ (n : Nat) (e : Expr), ¬ Step (num n) e := num_stuck
example {e₁ e₁' : Expr} (e₂ : Expr) : Star Step e₁ e₁' → Star Step (plus e₁ e₂) (plus e₁' e₂) :=
  star_plus_left e₂
example : Star Step (plus (plus (num 1) (num 2)) (num 3)) (num 6) := eval_example
