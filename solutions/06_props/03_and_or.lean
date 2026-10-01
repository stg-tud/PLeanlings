/-
# 06.03 — Conjunction is a pair, disjunction is a sum

In Lean, `P ∧ Q` (typed `\and`) is notation for `And P Q`, which is simply a
**structure** with two fields:

    structure And (a b : Prop) : Prop where
      intro ::
      left  : a
      right : b

So a proof of `P ∧ Q` is a *pair* of proofs, just like a value of
`Nat × String` is a pair of values:

* build it with the anonymous constructor `⟨hp, hq⟩` (type `\<` and `\>`),
* take it apart with `h.1` / `h.2` (or `h.left` / `h.right`).

`P ∨ Q` (typed `\or`) is `Or P Q`, an **inductive type with two
constructors**, just like a sum type / tagged union:

    inductive Or (a b : Prop) : Prop where
      | inl (h : a) : Or a b
      | inr (h : b) : Or a b

* build it with `Or.inl hp` or `Or.inr hq`,
* use it by **pattern matching**: you must handle both cases.

        fun h => match h with
          | Or.inl hp => …
          | Or.inr hq => …

| logic    | programming            |
|----------|------------------------|
| `P ∧ Q`  | product type `P × Q`   |
| `P ∨ Q`  | sum type `P ⊕ Q`       |

## Your task

Prove the three theorems with terms. Example:

    theorem and_left {P Q : Prop} : P ∧ Q → P := fun h => h.1
-/

theorem and_left {P Q : Prop} : P ∧ Q → P := fun h => h.1

theorem and_swap {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.2, h.1⟩

theorem or_swap {P Q : Prop} : P ∨ Q → Q ∨ P :=
  fun h => match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

theorem and_or_distrib {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  fun h => match h.2 with
    | Or.inl hq => Or.inl ⟨h.1, hq⟩
    | Or.inr hr => Or.inr ⟨h.1, hr⟩
