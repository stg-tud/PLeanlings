/-
# 09.02 — Rule induction

How do we prove something about *all* even numbers, like
"`Even n` implies `∃ k, n = 2 * k`"? Induction on `n` does not work well:
`Even (n + 1)` says nothing useful about `n`.

Instead we do induction on the **derivation** of `Even n`. This is called
**rule induction**: to prove that `P n` holds whenever `Even n` holds,
show that every rule *preserves* `P`:

* rule `zero`: show `P 0`;
* rule `ss`: assuming `Even n` *and the induction hypothesis* `P n`,
  show `P (n + 2)`.

In Lean:

    theorem foo (h : Even n) : P n := by
      induction h with
      | zero => …                -- ⊢ P 0
      | ss h ih => …             -- h : Even n, ih : P n ⊢ P (n + 2)

The number `n` in rule `ss` is an implicit argument, so Lean names it
`n✝` in the goal (an inaccessible name you cannot type). Write
`| @ss k h ih => …` to give it the name `k`.

It is the same `induction` tactic, because `Even` is an inductive type
whose values are derivation trees. You will prove type preservation for the
lambda calculus by exactly this kind of induction (on the typing or
evaluation derivation).

## Your task

Prove the three theorems. For the arithmetic side goals `omega` is your
friend; `exists k + 1` lets you pick a witness.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Even : Nat → Prop where
  | zero : Even 0
  | ss {n : Nat} : Even n → Even (n + 2)

/-! ## Your proofs -/

theorem even_double (k : Nat) : Even (2 * k) := by
  induction k with
  | zero => exact Even.zero
  | succ k ih =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h]
    exact Even.ss ih

theorem even_exists {n : Nat} (h : Even n) : ∃ k, n = 2 * k := by
  induction h with
  | zero => exists 0
  | ss h ih =>
    obtain ⟨j, hj⟩ := ih
    exists j + 1
    omega

theorem even_add {m n : Nat} (hm : Even m) (hn : Even n) : Even (m + n) := by
  induction hm with
  | zero => simp [hn]
  | @ss k h ih =>
    have e : k + 2 + n = (k + n) + 2 := by omega
    rw [e]
    exact Even.ss ih
