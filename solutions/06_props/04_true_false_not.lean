/-
# 06.04 — `True`, `False` and negation

Two more propositions complete the picture:

    inductive True : Prop where
      | intro : True          -- one constructor: trivially provable

    inductive False : Prop    -- no constructors at all!

`True` is like the unit type: `True.intro : True` (also written `trivial`).
`False` is like the *empty* type: there is no way to build a proof of it.
But if you *have* `h : False` (say, as a hypothesis), you can conclude
anything: `False.elim h : Q` for any `Q`. In programming terms, a function
out of the empty type can return anything, since it will never be called.

**Negation** is defined, not primitive:

    def Not (a : Prop) : Prop := a → False      -- written ¬ a  (\not)

So a proof of `¬ P` is a *function* that turns a (hypothetical) proof of `P`
into a proof of `False`; and if `hn : ¬ P` and `hp : P`, then `hn hp : False`.
The library helper `absurd hp hn : Q` combines this with `False.elim`.

Lean knows that different constructors are different: `0 = 1` is a
proposition, but it is false, and `by decide` proves `¬ (0 = 1)` (also
written `0 ≠ 1`).

## Your task

Prove the four theorems below with terms.
-/

theorem true_holds : True := True.intro

theorem double_neg_intro {P : Prop} : P → ¬¬P :=
  fun hp hn => hn hp

theorem contrapositive {P Q : Prop} : (P → Q) → ¬Q → ¬P :=
  fun hpq hnq hp => hnq (hpq hp)

theorem explode {P Q : Prop} : P → ¬P → Q :=
  fun hp hn => absurd hp hn

theorem not_or_split {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩

theorem zero_ne_one : 0 ≠ 1 := by decide
