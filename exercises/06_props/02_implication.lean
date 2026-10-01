/-
# 06.02 — Propositions as types: implication

The **Curry–Howard correspondence** says: propositions are types, and
proofs are programs. You already know the most important case:

| logic                | programming                 |
|----------------------|-----------------------------|
| proposition `P`      | type `P`                    |
| proof `h : P`        | term `h : P`                |
| implication `P → Q`  | function type `P → Q`       |

A proof of `P → Q` is a *function* that turns any proof of `P` into a proof
of `Q`. So we prove implications with `fun`:

    theorem self_imp (P : Prop) : P → P := fun hp => hp

This is the identity function! Compare it with `fun (x : Nat) => x`.
Using an implication `h : P → Q` on `hp : P` is function application:
`h hp : Q` (this is the logical rule *modus ponens*).

Arguments in curly braces `{P Q : Prop}` are *implicit*: Lean infers them,
so you can write `const_intro hp hq` instead of `const_intro P Q hp hq`.

The connection to type systems is literal: in the simply typed lambda
calculus, which you will build at the end of this course, the term
`λx. λy. x` has type `A → B → A`. Read as logic, that type is the tautology
"`A` implies (`B` implies `A`)", and the term is its proof.

## Your task

Write the proof terms (programs!) for the three theorems.
-/

theorem self_imp (P : Prop) : P → P := fun hp => hp

theorem const_intro {P Q : Prop} : P → Q → P :=
  sorry

theorem imp_trans {P Q R : Prop} : (P → Q) → (Q → R) → P → R :=
  sorry

theorem imp_dup {P Q : Prop} : (P → P → Q) → P → Q :=
  sorry
