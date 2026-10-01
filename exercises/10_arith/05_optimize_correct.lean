/-
# 10.05 — The optimizer is correct

An optimizer must not change what a program means. For our constant
folder that is a precise theorem:

    ∀ env e,  eval env (optimize e) = eval env e

This is the simplest instance of **compiler correctness**, a field that
goes all the way up to fully verified C compilers (CompCert) written in
proof assistants like Lean and Rocq.

The proof is in two steps.

**Step 1: the smart constructors are correct.** `mkPlus a b` must mean the
same as `plus a b`. To prove it, unfold `mkPlus` and use `split`: it
creates one goal per line of the `match`, with the pattern substituted in.
For the overlapping lines, `split` also adds hypotheses saying that the
earlier patterns did *not* match. In every case `simp_all [eval]` finishes
(the arithmetic facts `0 + b = b` etc. are simp lemmas):

```
theorem eval_mkPlus (env : Env) (a b : AExp) :
    eval env (mkPlus a b) = eval env a + eval env b := by
  unfold mkPlus
  split <;> simp_all [eval]
```

**Step 2: structural induction on `e`.** For `plus a b`, the optimizer
returns `mkPlus (optimize a) (optimize b)`. By step 1 this means
`eval env (optimize a) + eval env (optimize b)`, and by the induction
hypotheses that is `eval env a + eval env b`. You can hand all of these
facts to `simp`.

## Your task

Prove `eval_mkTimes` and `optimize_correct`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive AExp where
  | num   (n : Nat)
  | var   (x : String)
  | plus  (a b : AExp)
  | times (a b : AExp)
  deriving Repr, DecidableEq

def Env := String → Nat

def eval (env : Env) : AExp → Nat
  | .num n => n
  | .var x => env x
  | .plus a b => eval env a + eval env b
  | .times a b => eval env a * eval env b

def mkPlus : AExp → AExp → AExp
  | .num n, .num m => .num (n + m)
  | .num 0, b => b
  | a, .num 0 => a
  | a, b => .plus a b

def mkTimes : AExp → AExp → AExp
  | .num n, .num m => .num (n * m)
  | .num 0, _ => .num 0
  | _, .num 0 => .num 0
  | .num 1, b => b
  | a, .num 1 => a
  | a, b => .times a b

def optimize : AExp → AExp
  | .num n => .num n
  | .var x => .var x
  | .plus a b => mkPlus (optimize a) (optimize b)
  | .times a b => mkTimes (optimize a) (optimize b)

theorem eval_mkPlus (env : Env) (a b : AExp) :
    eval env (mkPlus a b) = eval env a + eval env b := by
  unfold mkPlus
  split <;> simp_all [eval]

/-! ## Exercises -/

theorem eval_mkTimes (env : Env) (a b : AExp) :
    eval env (mkTimes a b) = eval env a * eval env b := by
  sorry

theorem optimize_correct (env : Env) (e : AExp) :
    eval env (optimize e) = eval env e := by
  induction e with
  | num n => rfl
  | var x => rfl
  | plus a b iha ihb => sorry
  | times a b iha ihb => sorry
