/-
# 07.04 — Rewriting with `rw`

If you have an equation `h : a = b`, then `rw [h]` replaces every `a` in the
goal by `b`. Afterwards `rw` automatically tries `rfl`, so if the goal
became `x = x` it is closed.

* `rw [← h]` rewrites from right to left (`b` becomes `a`). Type `\l`.
* `rw [h1, h2]` rewrites with several equations in sequence.
* `rw [h] at h'` rewrites in the hypothesis `h'` instead of the goal.
* You can rewrite with theorems, too. Library lemmas such as
  `Nat.add_comm : ∀ n m, n + m = m + n` and `Nat.mul_comm` are equations
  with arguments; `rw [Nat.add_comm a b]` rewrites `a + b` to `b + a`.
  Without arguments, `rw [Nat.add_comm]` rewrites the first match it finds.

Example:

    theorem rw_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
      rw [h1]   -- ⊢ b = c
      rw [h2]   -- ⊢ c = c, closed by rfl automatically

In PL proofs, `rw` is what you do when you "substitute equals for equals".

## Your task

Prove the theorems using `rw` (no `omega` or `simp` yet!).
-/

theorem rw_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  rw [h2]

theorem rw_back (a b : Nat) (f : Nat → Nat) (h : f a = b) (hb : b = 7) : f a = 7 := by
  rw [h, hb]

theorem rw_at (a b : Nat) (h1 : a + 0 = b) (h2 : a = 3) : b = 3 := by
  rw [h2] at h1
  rw [← h1]

theorem rw_comm (a b c : Nat) : (a + b) * c = c * (b + a) := by
  rw [Nat.add_comm a b, Nat.mul_comm]
