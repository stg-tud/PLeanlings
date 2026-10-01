/-
# 07.05 — Computation: `unfold`, `simp`, `show`

When the goal mentions your own definitions, you often need to look inside.

* `unfold f` replaces `f` by its definition in the goal
  (`unfold f at h` in a hypothesis).
* `simp` is the **simplifier**: it rewrites the goal with a big database of
  simplification lemmas (`x + 0 = x`, `[] ++ l = l`, `a ∧ True ↔ a`, …)
  and closes it if it becomes `True`. Nothing magic: `simp` is a
  repeated `rw` with many known equations.
* `simp [f, h]` additionally unfolds definition `f` and rewrites with the
  hypothesis or lemma `h`. `simp at h` simplifies a hypothesis.
* `show T` changes the goal to `T` if `T` is the same up to computation
  (definitional unfolding). It is also nice documentation: it states
  what you expect the goal to be.

`simp` should close goals ("terminal simp") or be followed by more tactics.
If `simp` fails to make progress, it reports an error.

Example:

    def double (n : Nat) : Nat := n + n

    theorem double_two : double 2 = 4 := by
      unfold double   -- ⊢ 2 + 2 = 4
      rfl

## Your task

Prove the theorems below. The definitions are given.
-/

def double (n : Nat) : Nat := n + n

def swapPair (p : Nat × Nat) : Nat × Nat := (p.2, p.1)

theorem double_two : double 2 = 4 := by
  unfold double
  rfl

theorem double_zero_add (n : Nat) : double (0 + n) = n + n := by
  sorry

theorem swap_swap (p : Nat × Nat) : swapPair (swapPair p) = p := by
  sorry

theorem double_show (n : Nat) : double n = n + n := by
  sorry

theorem map_double (l : List Nat) (h : l = [1, 2]) : l.map double = [2, 4] := by
  sorry
