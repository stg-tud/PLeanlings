/-
# 10.03 — An interpreter

What does an expression *mean*? For arithmetic expressions the answer is
easy: a number. But `x + 1` only has a value once we know `x`. An
**environment** maps variables to their values:

```
def Env := String → Nat
```

(Real interpreters use association lists or hash maps. A function is the
simplest model and works just as well for proofs.)

An **interpreter** (or *evaluator*) computes the value of an expression in
an environment, by recursion on the AST:

    eval env (num n)     = n
    eval env (var x)     = env x
    eval env (plus a b)  = eval env a + eval env b
    eval env (times a b) = eval env a * eval env b

This style of semantics, "the meaning of a compound expression is computed
from the meanings of its parts", is called *denotational* or
*compositional*. Note what happens here: the *object language* `+` (the
constructor `plus`) is explained by the *meta language* `+` (Lean's
addition on `Nat`). That is typical for interpreters.

Because `eval` is an ordinary Lean function, we can both *run* it
(`#eval`) and *prove* things about it. Equations like the ones above hold
by definition, so `simp [eval]` can use them.

## Your task

1. Finish `eval`.
2. Prove `eval_plus_zero` and `eval_times_comm`: first `simp [eval]` to
   unfold the evaluator, then close the remaining arithmetic goal (if any)
   with `omega` or a library lemma such as `Nat.mul_comm`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive AExp where
  | num   (n : Nat)
  | var   (x : String)
  | plus  (a b : AExp)
  | times (a b : AExp)
  deriving Repr, DecidableEq

def Env := String → Nat

/-- The environment in which every variable is 0. -/
def Env.empty : Env := fun _ => 0

/-- `env.set x n` maps `x` to `n` and every other variable `y` to `env y`. -/
def Env.set (env : Env) (x : String) (n : Nat) : Env :=
  fun y => if y = x then n else env y

/-! ## Exercises -/

def eval (env : Env) : AExp → Nat
  | .num n => n
  | .var x => env x
  | .plus a b => eval env a + eval env b
  | .times a b => eval env a * eval env b

-- `2 + x * 3` with `x = 5`
#eval eval (Env.empty.set "x" 5) (.plus (.num 2) (.times (.var "x") (.num 3)))  -- 17

theorem eval_plus_zero (env : Env) (a : AExp) :
    eval env (.plus a (.num 0)) = eval env a := by
  simp [eval]

theorem eval_times_comm (env : Env) (a b : AExp) :
    eval env (.times a b) = eval env (.times b a) := by
  simp [eval, Nat.mul_comm]
