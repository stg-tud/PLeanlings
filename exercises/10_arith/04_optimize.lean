/-
# 10.04 — A constant-folding optimizer

Compilers do not translate programs naively: they first *optimize* the AST.
One of the simplest optimizations is **constant folding**, computing at
compile time whatever can already be computed:

    (2 + 3) * x    ⇒    5 * x
    x * (0 + 1)    ⇒    x
    y + 0 * z      ⇒    y

We implement it with **smart constructors**: functions `mkPlus a b` and
`mkTimes a b` that *build* a `plus`/`times` node but simplify on the way.
`optimize` then rebuilds the tree bottom-up, using the smart constructors
instead of the plain ones:

```
def mkPlus : AExp → AExp → AExp
  | .num n, .num m => .num (n + m)    -- n + m    ⇒  the number n+m
  | .num 0, b      => b               -- 0 + b    ⇒  b
  | a,      .num 0 => a               -- a + 0    ⇒  a
  | a,      b      => .plus a b       -- otherwise: no change
```

Lean tries the patterns of a `match` **from top to bottom** and takes the
first one that fits. So the patterns may overlap: the last line only
applies when none of the earlier ones did.

Constant folding is so simple that it is easy to get wrong, e.g. by
writing `0 * b ⇒ b` by accident. In the next exercise we will *prove* that
it preserves the meaning of every expression.

## Your task

1. Write `mkTimes`. It should implement these rules (in this order):

       n * m  ⇒  the number n*m
       0 * b  ⇒  0
       a * 0  ⇒  0
       1 * b  ⇒  b
       a * 1  ⇒  a
       a * b  ⇒  a * b      (otherwise)

2. Finish `optimize`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive AExp where
  | num   (n : Nat)
  | var   (x : String)
  | plus  (a b : AExp)
  | times (a b : AExp)
  deriving Repr, DecidableEq

def mkPlus : AExp → AExp → AExp
  | .num n, .num m => .num (n + m)
  | .num 0, b => b
  | a, .num 0 => a
  | a, b => .plus a b

/-! ## Exercises -/

def mkTimes : AExp → AExp → AExp
  | .num n, .num m => .num (n * m)
  | a, b => sorry

def optimize : AExp → AExp
  | .num n => .num n
  | .var x => .var x
  | .plus a b => sorry
  | .times a b => sorry
