/-
# 08.01 — Induction on `Nat`

Here is our own addition, defined by structural recursion on the *first*
argument:

    def add : Nat → Nat → Nat
      | 0,     m => m
      | n + 1, m => add n m + 1

`add 0 m = m` holds by definition (`rfl`). But `add n 0 = n` does **not**:
`add n 0` cannot compute, because `n` is an unknown variable. We need
**induction**:

> To prove `P n` for all `n : Nat`, prove `P 0` and prove that
> `P n` implies `P (n + 1)`.

In Lean:

    theorem add_zero (n : Nat) : add n 0 = n := by
      induction n with
      | zero => rfl                    -- ⊢ add 0 0 = 0
      | succ n ih =>                   -- ih : add n 0 = n
        simp [add, ih]                 -- ⊢ add (n + 1) 0 = n + 1

In the `succ` case, `ih` is the **induction hypothesis**. `simp [add]`
unfolds one step of `add`, turning `add (n + 1) 0` into `add n 0 + 1`, and
then `ih` rewrites `add n 0` to `n`. (`rw [add, ih]` or
`show add n 0 + 1 = n + 1; rw [ih]` work too.)

## Recursion = induction

Compare the proof with the definition: both have a case for `0` and a case
for `n + 1`, and in the latter we may use the result for `n`. The induction
hypothesis *is* the recursive call! You can even write the proof as a
recursive function, and Lean checks that it terminates (an infinite
"proof" would prove anything):

    theorem add_zero' : ∀ n, add n 0 = n
      | 0     => rfl
      | n + 1 => by simp [add, add_zero' n]

## Your task

Prove `add_zero` and `add_succ` by induction on `n`.
-/

def add : Nat → Nat → Nat
  | 0,     m => m
  | n + 1, m => add n m + 1

#eval add 2 3

theorem add_zero (n : Nat) : add n 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

theorem add_succ (n m : Nat) : add n (m + 1) = add n m + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]
