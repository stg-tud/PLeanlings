/-
# 09.01 — Inductive predicates: inference rules

PL papers define judgments by **inference rules**. Above the line are the
premises, below it the conclusion. For "`n` is even":

    ---------- (zero)          Even n
     Even 0                 ------------ (ss)
                            Even (n + 2)

Read: `0` is even; and if `n` is even, then `n + 2` is even. Nothing else
is even: a fact `Even n` holds only if it can be derived with these rules.

In Lean, such a rule system is an `inductive` *predicate*: a family of
propositions with one **constructor per rule**. Constructor arguments are
the premises, the result type is the conclusion:

    inductive Even : Nat → Prop where
      | zero : Even 0
      | ss {n : Nat} : Even n → Even (n + 2)

A proof of `Even 4` is a **derivation tree**, built from constructors:

    ---------- (zero)
     Even 0
    ---------- (ss)
     Even 2
    ---------- (ss)
     Even 4

which, as a term, is `Even.ss (Even.ss Even.zero)`. In tactic mode, work
backwards with `apply Even.ss` and finish with `exact Even.zero`.

**Inversion.** Why is `Even 1` false? No rule has a conclusion that matches
`Even 1`: `Even 0` doesn't, and `Even (n + 2)` would need `n + 2 = 1`. Given
`h : Even 1`, the tactic `cases h` tries every rule and finds that none
can apply, so the goal is closed. Similarly, `cases h` on `h : Even (n + 2)`
leaves only the `ss` case and gives you the premise `Even n`.

The whole rest of the course works like this: the typing judgment
`Γ ⊢ t : T` and the evaluation relation `t ⟶ t'` of the lambda calculus
will be inductive predicates, with one constructor per typing or evaluation
rule.

## Your task

Prove the four theorems.
-/

inductive Even : Nat → Prop where
  | zero : Even 0
  | ss {n : Nat} : Even n → Even (n + 2)

theorem even_two : Even 2 := Even.ss Even.zero

theorem even_six : Even 6 := by
  sorry

theorem not_even_one : ¬ Even 1 := by
  sorry

theorem even_inv (n : Nat) (h : Even (n + 2)) : Even n := by
  sorry

theorem not_even_three : ¬ Even 3 := by
  sorry
