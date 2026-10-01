/-
# 00.02 — Reading error messages

Lean is strict. When something is wrong it tells you exactly where, and
learning to read these messages is half the battle.

The definition below has a **type error**. `answer` is declared to have type
`Nat` (natural numbers 0, 1, 2, …), but the body is a `String`.
Hover over the red squiggle (or read the runner's output) to see the message:

    Type mismatch
      "42"
    has type
      String
    but is expected to have type
      Nat

## Your task

Fix the definition so that `answer` is the *number* 42.
-/

def answer : Nat := 42

#eval answer + 1
