/-
# 09.03 — `≤` as an inductive relation

Relations with two arguments are defined the same way. Here is "less than
or equal" as a rule system:

    ---------- (refl)          Le n m
     Le n n                ------------- (step)
                            Le n (m + 1)

    inductive Le : Nat → Nat → Prop where
      | refl (n : Nat) : Le n n
      | step {n m : Nat} : Le n m → Le n (m + 1)

This is not a toy: Lean's own `Nat.le`, the `≤` on natural numbers, is
defined exactly like this!

Rule induction on `h : Le n m` gives one case per rule:

    induction h with
    | refl => …              -- ⊢ P n n
    | step h ih => …         -- h : Le n m, ih : P n m ⊢ P n (m + 1)

Tip: to prove `Le a c` from `Le a b` and `Le b c`, do induction on the
*second* derivation: its `refl` case gives `c = b` and its `step` case
adds one more `step` at the end.

## Your task

Prove the four theorems.
-/

inductive Le : Nat → Nat → Prop where
  | refl (n : Nat) : Le n n
  | step {n m : Nat} : Le n m → Le n (m + 1)

theorem le_three_five : Le 3 5 := by
  apply Le.step
  apply Le.step
  exact Le.refl 3

theorem le_zero (n : Nat) : Le 0 n := by
  induction n with
  | zero => exact Le.refl 0
  | succ n ih => exact Le.step ih

theorem le_trans {a b c : Nat} (hab : Le a b) (hbc : Le b c) : Le a c := by
  induction hbc with
  | refl => exact hab
  | step _ ih => exact Le.step ih

theorem le_sound {n m : Nat} (h : Le n m) : n ≤ m := by
  induction h with
  | refl => omega
  | step _ ih => omega
