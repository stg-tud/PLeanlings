/-
# 08.04 — Reversing twice

Naive list reversal: reverse the tail, then append the head at the end.

    def rev : List α → List α
      | []      => []
      | x :: xs => app (rev xs) [x]

We want to prove `rev (rev xs) = xs`. Trying induction directly gets stuck
in the `cons` case at `rev (app (rev xs) [x]) = x :: xs`: we need to know
how `rev` interacts with `app`. That is a typical situation: **to prove
the theorem you want, first prove a more general helper lemma**. Here the
chain of lemmas is:

1. `app_nil : app xs [] = xs`
2. `app_assoc : app (app xs ys) zs = app xs (app ys zs)`
3. `rev_app : rev (app xs ys) = app (rev ys) (rev xs)` (uses 1 and 2)
4. `rev_rev : rev (rev xs) = xs` (uses 3)

Use earlier lemmas by passing them to `simp`, e.g. `simp [rev, app, app_nil]`,
or with `rw`.

## Your task

Prove the four lemmas.
-/

/-! ## Given (from earlier exercises) — do not edit -/

def app {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys

/-! ## New -/

def rev {α : Type} : List α → List α
  | []      => []
  | x :: xs => app (rev xs) [x]

#eval rev [1, 2, 3]

theorem app_nil {α : Type} (xs : List α) : app xs [] = xs := by
  sorry

theorem app_assoc {α : Type} (xs ys zs : List α) :
    app (app xs ys) zs = app xs (app ys zs) := by
  sorry

theorem rev_app {α : Type} (xs ys : List α) : rev (app xs ys) = app (rev ys) (rev xs) := by
  sorry

theorem rev_rev {α : Type} (xs : List α) : rev (rev xs) = xs := by
  sorry
