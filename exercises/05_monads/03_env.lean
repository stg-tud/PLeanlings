/-
# 05.03 — An interpreter with variables and errors

Let's extend the expression language from chapter 03 with **variables** and
**division**. The value of a variable comes from an **environment**: a list
of (name, value) pairs, called an *association list*:

    def env : Env := [("x", 5), ("y", 0)]

Two things can now go wrong during evaluation: a variable may be unbound
(not in the environment), and we may divide by zero. Our interpreter
therefore returns `Except String Nat`.

This is a miniature version of what you will build later in the course: an
interpreter and a type checker that walk over a syntax tree and report
errors with `Except`.

## Your task

1. `lookup env x` finds the value of `x` in `env` (the *first* pair with
   name `x` wins). If there is none, fail with exactly
   `s!"unbound variable: {x}"`.
2. `eval env e` evaluates `e`. Division by zero fails with exactly
   `"division by zero"`. Use `do` notation for the recursive cases.
-/

abbrev Env := List (String × Nat)

inductive Expr where
  | num  (n : Nat)
  | var  (x : String)
  | plus (a b : Expr)
  | div  (a b : Expr)
deriving Repr

def lookup (env : Env) (x : String) : Except String Nat :=
  match env with
  | []             => sorry
  | (y, v) :: rest => sorry

def eval (env : Env) : Expr → Except String Nat
  | .num n    => sorry
  | .var x    => sorry
  | .plus a b => sorry
  | .div a b  => sorry

def env : Env := [("x", 5), ("y", 0)]
