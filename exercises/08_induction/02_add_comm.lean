/-
# 08.02 — Commutativity and associativity

With the two lemmas from the previous exercise you can now prove the classic
laws for our own `add`.

Tips:

* Use the lemmas! `rw [add_zero]` or `simp [add, add_succ, ih]`.
  A proof by induction usually needs lemmas about the *other* argument,
  which is why we proved `add_zero` and `add_succ` first.
* Induct on the variable that the function recurses on (here: the first
  argument of `add`). That is where computation happens.
* If you get stuck, look at the goal in the `succ` case and ask: which
  equation would turn it into something about `n` so that `ih` applies?

## Your task

Prove `add_comm` and `add_assoc`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

def add : Nat → Nat → Nat
  | 0,     m => m
  | n + 1, m => add n m + 1

theorem add_zero (n : Nat) : add n 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

theorem add_succ (n m : Nat) : add n (m + 1) = add n m + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

/-! ## Your proofs -/

theorem add_comm (n m : Nat) : add n m = add m n := by
  sorry

theorem add_assoc (a b c : Nat) : add (add a b) c = add a (add b c) := by
  sorry
