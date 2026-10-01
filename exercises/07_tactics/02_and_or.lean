/-
# 07.02 — Tactics for `∧` and `∨`

**Proving** (the connective is in the goal):

* goal `P ∧ Q`: `constructor` splits it into two goals `P` and `Q`.
* goal `P ∨ Q`: `left` reduces it to `P`, `right` to `Q`.
  (These are just `apply Or.inl` and `apply Or.inr`.)

**Using** (the connective is in a hypothesis `h`):

* `cases h with | intro hp hq => …` takes `h : P ∧ Q` apart.
  For `h : P ∨ Q` you get two goals, one per constructor:

      cases h with
      | inl hp => …
      | inr hq => …

* `obtain ⟨hp, hq⟩ := h` is a shorter way to take apart `h : P ∧ Q`, and
  `obtain hp | hq := h` splits `h : P ∨ Q` into two goals.
* `rcases h with ⟨hp, hq⟩` / `rcases h with hp | hq` is the same.
  Patterns nest: `rcases h with ⟨hp, hq | hr⟩` splits `P ∧ (Q ∨ R)`.

Example:

    theorem and_swap {P Q : Prop} (h : P ∧ Q) : Q ∧ P := by
      obtain ⟨hp, hq⟩ := h
      constructor
      · exact hq
      · exact hp

## Your task

Prove the theorems with tactics. Try a different style each time.
-/

theorem and_swap {P Q : Prop} (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hp, hq⟩ := h
  constructor
  · exact hq
  · exact hp

theorem or_swap {P Q : Prop} (h : P ∨ Q) : Q ∨ P := by
  sorry

theorem or_and_distrib {P Q R : Prop} (h : (P ∧ Q) ∨ (P ∧ R)) : P ∧ (Q ∨ R) := by
  sorry

theorem and_assoc' {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  sorry
