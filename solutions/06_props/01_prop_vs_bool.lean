/-
# 06.01 — `Prop` versus `Bool`

Welcome to Part II: Lean as a *proof assistant*.

So far you have computed with `Bool`: `3 < 5` used inside an `if` evaluates
to `true` or `false`. A `Bool` is **data**: one bit that a program computes.

Lean has a second, very different kind of truth value: `Prop`, the type of
**propositions** (statements). Statements are things you *prove*:

    #check (2 + 2 = 4)          -- 2 + 2 = 4 : Prop
    #check (∀ n : Nat, n + 0 = n) -- … : Prop
    #check (2 + 2 = 5)          -- also a Prop! (a false one)

A proposition is not evaluated to true/false. Instead, a proposition is a
**type**, and a *proof* of it is a **term of that type**. To state and prove
something, we write

    theorem name : statement := proof

(`theorem` is just `def` for proofs.) Two ways to build proofs for now:

* `rfl` ("reflexivity") proves `a = a`. Lean will compute both sides, so
  `rfl` also proves `2 + 2 = 4` or `[1] ++ [2] = [1, 2]`: both sides
  evaluate to the same value.
* `by decide` asks Lean to decide a *decidable* proposition by running an
  algorithm, e.g. comparisons of numbers `3 * 7 < 22` or `10 ≠ 11`. Here
  `by` starts a *tactic script* (a small program that builds the proof
  for you); much more on tactics in chapter 07.

`decide` is the bridge between the two worlds: for a decidable `p : Prop`,
`decide p : Bool` computes the bit, and if it is `true`, then `p` holds.

    #eval decide (3 < 5)        -- true

Also note: `b = true` turns a `Bool` `b` into a `Prop`. Lean usually
inserts this automatically, so `isSmall 3` can be used as a statement.

## Your task

Prove the four theorems below. Use `rfl` for equations and `by decide` for
the others.
-/

def isSmall (n : Nat) : Bool := n < 5

#eval isSmall 3
#check (isSmall 3 = true)

theorem two_plus_two : 2 + 2 = 4 := rfl

theorem append_example : [1, 2] ++ [3] = [1, 2, 3] := rfl

theorem lt_example : 3 * 7 < 22 := by decide

theorem small_three : isSmall 3 = true := by decide
