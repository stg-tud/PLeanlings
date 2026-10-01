/-
# 10.02 — Pretty-printing

A parser turns concrete syntax into an AST. The opposite direction, turning
an AST back into text, is called **pretty-printing**. Every compiler needs
one, for error messages if nothing else.

The easiest way is to put parentheses around *every* compound expression:

    plus (num 2) (times (var "x") (num 3))   ↦   "(2 + (x * 3))"

That is always correct but ugly. A nicer printer only adds parentheses
where they are needed. The standard trick is to give every operator a
**precedence level** and to pass down the level of the context we are
printing in:

| node      | level |
|-----------|-------|
| `plus`    | 1     |
| `times`   | 2     |

A node of level `p` printed in a context of level `ctx` needs parentheses
exactly when `ctx > p`. At the top level the context is 0.

What context do the operands get? Since `+` associates to the left,
`a + b + c` means `(a + b) + c`. So the *left* operand of `+` may itself be
a `+` without parentheses (print it at context 1), but the *right* operand
may not (print it at context 2). Likewise for `*`:

* `plus a b`:  parentheses when `ctx > 1`; print `a` at 1, `b` at 2.
* `times a b`: parentheses when `ctx > 2`; print `a` at 2, `b` at 3.

Numbers and variables never need parentheses.

## Your task

Fill in the `plus` and `times` cases of both printers.
Use `toString n` to print a number and `++` to concatenate strings.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive AExp where
  | num   (n : Nat)
  | var   (x : String)
  | plus  (a b : AExp)
  | times (a b : AExp)
  deriving Repr, DecidableEq

/-! ## Exercises -/

/-- Fully parenthesised printing: `(2 + (x * 3))`. -/
def AExp.toStr : AExp → String
  | .num n => toString n
  | .var x => x
  | .plus a b => "(" ++ a.toStr ++ " + " ++ b.toStr ++ ")"
  | .times a b => "(" ++ a.toStr ++ " * " ++ b.toStr ++ ")"

/-- Wrap `s` in parentheses if `b` is true. -/
def parenIf (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

/-- Precedence-aware printing at context level `ctx`. -/
def AExp.prettyAt (ctx : Nat) : AExp → String
  | .num n => toString n
  | .var x => x
  | .plus a b => parenIf (ctx > 1) (a.prettyAt 1 ++ " + " ++ b.prettyAt 2)
  | .times a b => parenIf (ctx > 2) (a.prettyAt 2 ++ " * " ++ b.prettyAt 3)

def AExp.pretty (e : AExp) : String := e.prettyAt 0

#eval (AExp.plus (.num 2) (.times (.var "x") (.num 3))).toStr    -- "(2 + (x * 3))"
#eval (AExp.plus (.num 2) (.times (.var "x") (.num 3))).pretty   -- "2 + x * 3"
#eval (AExp.times (.plus (.num 2) (.var "x")) (.num 3)).pretty   -- "(2 + x) * 3"
