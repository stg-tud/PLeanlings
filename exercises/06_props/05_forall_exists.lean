/-
# 06.05 — `∀` and `∃`: dependent functions and pairs

Quantifiers fit Curry–Howard too:

* A proof of `∀ n : Nat, P n` is a **function** that takes any `n` and
  returns a proof of `P n`. Its result *type* depends on the *argument*,
  so it is a *dependent* function type. Indeed `P → Q` is just the special
  case of `∀ _ : P, Q` where `Q` does not mention the argument.

      theorem add_zero_all : ∀ n : Nat, n + 0 = n := fun n => rfl

  Using it is application: `add_zero_all 5 : 5 + 0 = 5`.

* A proof of `∃ n : Nat, P n` is a **pair** of a *witness* `n` and a proof
  of `P n`: `⟨3, h⟩` where `h : P 3`. This is a *dependent* pair: the type
  of the second component depends on the first.

      theorem exists_double : ∃ n : Nat, n + n = 6 := ⟨3, rfl⟩

  To use `h : ∃ n, P n`, pattern match: `match h with | ⟨w, hw⟩ => …`.

Fun fact for PL people: `∀` corresponds to polymorphism / dependent function
types (Π-types) and `∃` to abstract types / Σ-types.

## Your task

Prove the theorems below with terms.
-/

theorem add_zero_all : ∀ n : Nat, n + 0 = n := fun _ => rfl

theorem exists_double : ∃ n : Nat, n + n = 6 := ⟨3, rfl⟩

-- Use `add_zero_all`.
theorem seven_add_zero : 7 + 0 = 7 := sorry

theorem exists_big : ∃ n : Nat, 10 < n := sorry

theorem forall_and_left {P Q : Nat → Prop} :
    (∀ n, P n ∧ Q n) → ∀ n, P n :=
  sorry

theorem exists_weaken {P Q : Nat → Prop} :
    (∃ n, P n ∧ Q n) → ∃ n, P n :=
  sorry
