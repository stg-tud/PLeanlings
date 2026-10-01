/-
# 13.01 — The untyped lambda calculus: syntax

The **lambda calculus** is the smallest "real" programming language. It has
only three kinds of terms:

    t ::= x          variable
        | λx. t      abstraction (an anonymous function with parameter x)
        | t₁ t₂      application (call t₁ with argument t₂)

That's it: no numbers, no booleans, no `if`. Yet it is Turing complete, and
every functional language (Lean included!) is built on top of it.

Conventions on paper:
* Application associates to the **left**: `f a b` means `(f a) b`.
* The body of a `λ` extends as far to the right as possible:
  `λx. x y` means `λx. (x y)`, not `(λx. x) y`.
* `λx y. t` abbreviates `λx. λy. t` (functions of several arguments are
  curried, exactly like in Lean).

In Lean we represent terms as an abstract syntax tree, with variable names
as strings:

    inductive Term where
      | var (x : String)
      | lam (x : String) (body : Term)
      | app (f a : Term)

Some famous terms:

| name | paper              | meaning                          |
|------|--------------------|----------------------------------|
| I    | `λx. x`            | the identity                     |
| K    | `λx y. x`          | constant function: ignores `y`   |
| S    | `λx y z. x z (y z)`| "apply with shared argument"     |
| ω    | `λx. x x`          | self-application                 |

## Free variables

In `λx. t` the `λ` **binds** `x` inside `t`. A variable occurrence that is
not bound by any enclosing `λ` is **free**. In `λx. x y`, `x` is bound and
`y` is free. A term without free variables is **closed** (a "complete
program").

    fv(x)      = [x]
    fv(λx. t)  = fv(t) with every x removed
    fv(t₁ t₂)  = fv(t₁) ++ fv(t₂)

## Your task

1. Define `K`, `S` and `omega` (ω) as `Term`s. `I` is done for you.
   Remember: `f a b` is `app (app f a) b`.
2. Implement `fv` following the equations above. Keep duplicates and the
   order of the equations (the checks compare lists exactly).
   `List.filter` and `!=` will be useful.
-/

inductive Term where
  | var (x : String)
  | lam (x : String) (body : Term)
  | app (f a : Term)
  deriving Repr, DecidableEq, Inhabited

open Term

/-- `λx. x` -/
def I : Term := lam "x" (var "x")

/-- `λx. λy. x` -/
def K : Term := sorry

/-- `λx. λy. λz. x z (y z)` -/
def S : Term := sorry

/-- `λx. x x` -/
def omega : Term := sorry

/-- The free variables of a term (with duplicates, left to right). -/
def fv : Term → List String
  | var x => sorry
  | lam x b => sorry
  | app f a => sorry

/-- A term is closed if it has no free variables. -/
def closed (t : Term) : Bool := (fv t).isEmpty

