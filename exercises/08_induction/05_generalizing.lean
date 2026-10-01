/-
# 08.05 — Generalizing the induction hypothesis

`rev` from the last exercise is slow (quadratic). The efficient version uses
an **accumulator**, like a tail-recursive loop:

    def revAcc : List α → List α → List α
      | [],      acc => acc
      | x :: xs, acc => revAcc xs (x :: acc)

We want `revAcc xs acc = app (rev xs) acc`. Try `induction xs` naively:
in the `cons` case the induction hypothesis is

    ih : revAcc xs acc = app (rev xs) acc

for the *fixed* `acc` from the statement. But the goal unfolds to
`revAcc xs (x :: acc) = …`, a *different* accumulator, so `ih` is useless!

The fix: make the induction hypothesis hold **for all** accumulators.

    induction xs generalizing acc with …

Now `ih : ∀ acc, revAcc xs acc = app (rev xs) acc`, and you can use it with
`ih (x :: acc)`, or just pass `ih` to `simp`. (Writing the statement as
`∀ acc, …` and doing `induction` before `intro acc` has the same effect.)

In recursive programs this is perfectly natural: the recursive call is made
with a *different* accumulator, so the "recursive call" in the proof must be
allowed to use a different one too. You will need `generalizing` in the STLC
proofs later, for example to generalize over the typing context.

## Your task

Prove `revAcc_eq`, `fastRev_eq` and `sumAcc_eq`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

def app {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys

def rev {α : Type} : List α → List α
  | []      => []
  | x :: xs => app (rev xs) [x]

theorem app_nil {α : Type} (xs : List α) : app xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]

theorem app_assoc {α : Type} (xs ys zs : List α) :
    app (app xs ys) zs = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]

/-! ## New -/

def revAcc {α : Type} : List α → List α → List α
  | [],      acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def fastRev {α : Type} (xs : List α) : List α := revAcc xs []

def sum : List Nat → Nat
  | []      => 0
  | x :: xs => x + sum xs

def sumAcc : List Nat → Nat → Nat
  | [],      acc => acc
  | x :: xs, acc => sumAcc xs (acc + x)

theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = app (rev xs) acc := by
  sorry

theorem fastRev_eq {α : Type} (xs : List α) : fastRev xs = rev xs := by
  sorry

theorem sumAcc_eq (xs : List Nat) (acc : Nat) : sumAcc xs acc = sum xs + acc := by
  sorry
