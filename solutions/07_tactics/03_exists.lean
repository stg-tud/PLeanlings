/-
# 07.03 — Tactics for `∃`

**Proving** `∃ x, P x`: provide a witness.

* `exists 3` uses `3` as the witness and then tries to close the remaining
  goal `P 3` automatically (with `rfl`-like reasoning).
* `refine ⟨3, ?_⟩` uses `3` as witness and leaves `P 3` as a new goal.
  `?_` marks a hole that becomes a goal.
* `exact ⟨3, h⟩` if you already have `h : P 3`.

**Using** `h : ∃ x, P x`: `obtain ⟨w, hw⟩ := h` gives you a fresh `w`
and `hw : P w`. (Or `cases h with | intro w hw => …`.)
You cannot choose `w`: you only know that *some* `w` exists.

Example:

    theorem exists_pos : ∃ n : Nat, 0 < n := by
      exists 1

## Your task

Prove the theorems below.
-/

theorem exists_pos : ∃ n : Nat, 0 < n := by
  exists 1

theorem exists_sum : ∃ a b : Nat, a + b = 5 ∧ a = b + 1 := by
  exists 3, 2

theorem exists_of_forall {P : Nat → Prop} (h : ∀ n, P n) : ∃ n, P n := by
  exact ⟨0, h 0⟩

theorem exists_and_comm {P Q : Nat → Prop} (h : ∃ n, P n ∧ Q n) : ∃ n, Q n ∧ P n := by
  obtain ⟨w, hp, hq⟩ := h
  exact ⟨w, hq, hp⟩
