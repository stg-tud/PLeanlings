/-
# 03.05 — Termination

Lean insists that every function **terminates**. Why? Suppose Lean accepted

    def loop (n : Nat) : Nat := loop n + 1

Then `loop 0 = loop 0 + 1` would be a true equation, and subtracting
`loop 0` on both sides "proves" `0 = 1`. Since Lean is also a proof
assistant (chapter 06 onwards), such a function would make the logic
inconsistent. So Lean only accepts a recursive definition if it can see
that it terminates.

* **Structural recursion** (calls on sub-parts, like `n` in `succ n` or `xs`
  in `x :: xs`) is accepted automatically.
* Otherwise Lean looks for a **measure**: a natural number that gets
  smaller in every recursive call. Often it finds one by itself:

      def digitSum (n : Nat) : Nat :=
        if n < 10 then n else n % 10 + digitSum (n / 10)

  Here `n` is the measure: `n / 10 < n` whenever `n ≥ 10`.
* When Lean cannot find the measure, you state it with `termination_by`,
  written after the function body. Lean then proves that it decreases
  (and asks for help with `decreasing_by` if it cannot).

(`partial def` turns the check off, but then you can't reason about the
function in proofs. We will not use it.)

## Your task

1. `interleave` alternates between the two lists:
   `interleave [1, 2, 3] [10, 20] = [1, 10, 2, 20, 3]`. The definition is
   correct, but Lean cannot prove termination: neither `xs` nor `ys`
   gets smaller in the recursive call, because they swap places! Read the
   error, then add a `termination_by` clause with a measure that does
   decrease.
2. Write `digitSum` as shown above.
-/

def interleave (xs ys : List Nat) : List Nat :=
  match xs with
  | []       => ys
  | x :: xs' => x :: interleave ys xs'

def digitSum (n : Nat) : Nat :=
  sorry
