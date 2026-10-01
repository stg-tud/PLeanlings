/-
# 07.01 — Tactic mode: `intro`, `exact`, `apply`

Writing proof terms by hand gets painful for bigger proofs. Instead, we can
write `by` followed by **tactics**: commands that build the proof term step
by step, working *backwards* from the goal.

## Reading the infoview

Put your cursor inside a `by` block. The infoview shows the **goal state**:

    P Q R : Prop
    hpq : P → Q
    hqr : Q → R
    ⊢ P → R

Above the turnstile `⊢` are the **hypotheses** (what you have, with names);
below it is the **goal** (what you must prove). Each tactic changes the
goal state. When no goals are left, the infoview says `No goals` and the
proof is done. Move the cursor line by line to watch the state change.

## Three basic tactics

* `intro h` — if the goal is `P → Q`, assume `h : P`; the goal becomes `Q`.
  (Also works for `∀ x, …` and for `¬ P`, which is `P → False`.)
  `intro h1 h2 h3` introduces several at once.
* `exact e` — close the goal with the term `e`, which must have exactly the
  goal's type, e.g. `exact hp`.
* `apply h` — if `h : P → Q` and the goal is `Q`, reduce the goal to `P`
  ("to prove `Q`, it suffices to prove `P`"). With more premises,
  `h : A → B → Q`, you get one new goal per premise.

Example:

    theorem imp_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) : P → R := by
      intro hp      -- hp : P        ⊢ R
      apply hqr     --               ⊢ Q
      apply hpq     --               ⊢ P
      exact hp      -- No goals

Note that hypotheses can be written before the colon, as named arguments.

When a tactic creates several goals, you solve them in order. To keep
proofs readable, focus on one goal at a time with a bullet `·` (typed `\.`):

    apply h      -- two new goals
    · exact h1   -- solves the first
    · exact h2   -- solves the second

## Your task

Prove the theorems using `intro`, `exact` and `apply` (no `fun`).
-/

theorem imp_trans {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  apply hqr
  apply hpq
  exact hp

theorem swap_args {P Q R : Prop} : (P → Q → R) → Q → P → R := by
  sorry

theorem apply_forall {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (h5 : P 5) : Q 5 := by
  sorry

theorem not_imp_intro {P Q : Prop} (hnq : ¬Q) (hpq : P → Q) : ¬P := by
  sorry
