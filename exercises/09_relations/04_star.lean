/-
# 09.04 — Reflexive–transitive closure

Operational semantics usually defines a **single step** `t ⟶ t'` and then
"evaluates in many steps", `t ⟶* t'`: zero or more single steps. The
many-step relation is the *reflexive–transitive closure* of the single-step
relation. We define it once, for any relation `R`:

    ------------ (refl)       R a b    Star R b c
     Star R a a               -------------------- (step)
                                   Star R a c

    inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
      | refl a : Star R a a
      | step : R a b → Star R b c → Star R a c

So a proof of `Star R a c` is a *chain* `a R b₁ R b₂ R … R c`, built like a
list: `refl` is the empty chain and `step` puts one more `R`-step in front.

Note that `R` is a *parameter*: `Star` takes a relation and returns a
relation. We will use `Star Step` for multi-step evaluation of lambda terms.

We name the lemmas `Star.single`, `Star.trans`, … so that dot notation works:
for `h : Star R a b` you may write `h.trans h'`.

## Your task

1. `Star.single`: one step is a chain.
2. `Star.trans`: chains can be concatenated (rule induction on the first).
3. `Star.tail`: a step can be added at the end (use the lemmas above).
4. Prove that `5` reaches `2` in the "count down" relation `Dec`.
-/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

theorem Star.single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b := by
  sorry

theorem Star.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  sorry

theorem Star.tail {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : Star R a b) (h2 : R b c) : Star R a c := by
  sorry

inductive Dec : Nat → Nat → Prop
  | dec (n : Nat) : Dec (n + 1) n

theorem five_to_two : Star Dec 5 2 := by
  sorry
