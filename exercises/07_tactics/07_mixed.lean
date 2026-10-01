/-
# 07.07 — Putting it together

Time to combine tactics. A small cheat sheet:

| goal / hypothesis  | prove (in goal)             | use (in hypothesis `h`)      |
|--------------------|-----------------------------|------------------------------|
| `P → Q`, `∀ x, P x`| `intro`                     | `apply h`, `h a`, `exact`    |
| `P ∧ Q`            | `constructor`, `⟨_, _⟩`     | `obtain ⟨hp, hq⟩ := h`       |
| `P ∨ Q`            | `left` / `right`            | `cases h` (two goals)        |
| `∃ x, P x`         | `exists w`, `⟨w, _⟩`        | `obtain ⟨w, hw⟩ := h`        |
| `¬ P`              | `intro hp` (goal `False`)   | `exfalso; apply h`           |
| `a = b`            | `rfl`, `simp`, `omega`      | `rw [h]`, `simp [h]`         |
| `False`            | (from a contradiction)      | `contradiction`              |

Below, `step` is a tiny "machine": it counts down by one, but never below 0.

## Your task

Prove the four theorems.
-/

def step (n : Nat) : Nat := n - 1

theorem step_lt (n : Nat) (h : 0 < n) : step n < n := by
  sorry

theorem step_exists (n : Nat) : ∃ m, step m = n ∧ n < m := by
  sorry

theorem step_cases (n : Nat) : step n = 0 ∨ step n + 1 = n := by
  sorry

theorem no_fixpoint (n : Nat) (h : step n = n) (hn : n ≠ 0) : False := by
  sorry
