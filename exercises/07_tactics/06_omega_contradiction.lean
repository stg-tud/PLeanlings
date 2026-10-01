/-
# 07.06 — `omega`, `contradiction`, `exfalso`, `have`

**Arithmetic.** `omega` is a decision procedure for *linear arithmetic*
over `Nat` and `Int`: `+`, `-`, `*` by constants, `<`, `≤`, `=`, `∧`, `∨`,
`¬`, … It uses the hypotheses in the context. It does not know your own
functions (unfold them first) and cannot do `x * y`.

    example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega

**Contradictions.** Sometimes the hypotheses are inconsistent, and then
any goal holds.

* `contradiction` closes the goal if the context contains something obviously
  impossible: `h : False`, both `h : P` and `h' : ¬ P`, or an equation
  between different constructors such as `h : 0 = 1` or `h : [] = x :: xs`.
* `exfalso` changes any goal to `False` ("I will derive a contradiction").
  Then you can `apply hn` for some `hn : ¬ P`.

**Intermediate facts.** `have h : P := proof` (or `have h : P := by tac`)
adds a new hypothesis `h : P` to the context. Use it to structure proofs into
steps, just like a `let` in a program.

## Your task

Prove the theorems below.
-/

theorem lin (a b : Nat) (h1 : a + 3 ≤ b) (h2 : b < 10) : a < 7 := by
  sorry

theorem from_false {P : Prop} (n : Nat) (h : n + 1 = 0) : P := by
  sorry

theorem from_not {P Q : Prop} (hp : P) (hn : ¬P) : Q := by
  sorry

theorem with_have (f : Nat → Nat) (hf : ∀ n, f n = n + 1) : f (f 0) = 2 := by
  have h0 : f 0 = 1 := hf 0
  sorry
