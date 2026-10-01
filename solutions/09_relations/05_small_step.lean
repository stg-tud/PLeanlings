/-
# 09.05 — A first small-step semantics

Let's put everything together on a tiny language of arithmetic expressions:

    inductive Expr where
      | num  : Nat → Expr
      | plus : Expr → Expr → Expr

The **small-step operational semantics** `e ⟶ e'` says how an expression
takes one computation step. We evaluate left to right:

    ----------------------------------- (plus_nums)
     plus (num n) (num m) ⟶ num (n + m)

               e₁ ⟶ e₁'
    ------------------------------ (plus_left)
     plus e₁ e₂ ⟶ plus e₁' e₂

                    e₂ ⟶ e₂'
    -------------------------------------- (plus_right)
     plus (num n) e₂ ⟶ plus (num n) e₂'

The rules `plus_left` and `plus_right` are *congruence* rules: they say
where in an expression the next step happens. The STLC semantics later
in the course has exactly this shape (with `β`-reduction instead of
`plus_nums`).

Many-step evaluation is `Star Step`.

## Your task

1. `one_step`: derive a single step.
2. `num_stuck`: a number does not step (it is a *value*). This kind of
   inversion lemma is used in the progress theorem.
3. `star_plus_left`: lift a many-step evaluation of the left operand to the
   whole `plus` (rule induction on the `Star`).
4. `eval_example`: evaluate `(1 + 2) + 3` to `6` in many steps.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

theorem Star.single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
  Star.step h (Star.refl b)

theorem Star.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  induction h1 with
  | refl => exact h2
  | step hab _ ih => exact Star.step hab (ih h2)

/-! ## New -/

inductive Expr where
  | num  : Nat → Expr
  | plus : Expr → Expr → Expr

open Expr

inductive Step : Expr → Expr → Prop
  | plus_nums (n m : Nat) : Step (plus (num n) (num m)) (num (n + m))
  | plus_left {e₁ e₁' : Expr} (e₂ : Expr) : Step e₁ e₁' → Step (plus e₁ e₂) (plus e₁' e₂)
  | plus_right (n : Nat) {e₂ e₂' : Expr} : Step e₂ e₂' → Step (plus (num n) e₂) (plus (num n) e₂')

theorem one_step : Step (plus (plus (num 1) (num 2)) (num 3)) (plus (num 3) (num 3)) := by
  apply Step.plus_left
  exact Step.plus_nums 1 2

theorem num_stuck (n : Nat) (e : Expr) : ¬ Step (num n) e := by
  intro h
  cases h

theorem star_plus_left {e₁ e₁' : Expr} (e₂ : Expr) (h : Star Step e₁ e₁') :
    Star Step (plus e₁ e₂) (plus e₁' e₂) := by
  induction h with
  | refl => exact Star.refl _
  | step hs _ ih => exact Star.step (Step.plus_left e₂ hs) ih

theorem eval_example : Star Step (plus (plus (num 1) (num 2)) (num 3)) (num 6) := by
  apply Star.step one_step
  apply Star.step (Step.plus_nums 3 3)
  exact Star.refl _
