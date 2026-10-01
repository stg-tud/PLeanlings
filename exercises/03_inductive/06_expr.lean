/-
# 03.06 — A first taste: expression trees

Here is a tiny programming language of arithmetic expressions, represented
as a tree (its **abstract syntax tree**, AST):

    inductive Expr where
      | num   (n : Nat)        -- a literal number
      | plus  (a b : Expr)     -- a + b
      | times (a b : Expr)     -- a * b

The expression `(1 + 2) * 3` becomes
`Expr.times (Expr.plus (Expr.num 1) (Expr.num 2)) (Expr.num 3)`.
Note how the parentheses disappeared: the tree structure already says
what belongs together.

An **interpreter** for this language is a recursive function from `Expr`
to the values (here: `Nat`). It evaluates the sub-expressions and combines
the results. This is the core idea of every interpreter, and you will
build much bigger ones in chapter 10 and later.

## Your task

1. `Expr.eval e` computes the value of `e`.
2. `Expr.countNums e` counts the number literals (`num`) in `e`.
-/

inductive Expr where
  | num   (n : Nat)
  | plus  (a b : Expr)
  | times (a b : Expr)
deriving Repr

def Expr.eval : Expr → Nat
  | .num n     => sorry
  | .plus a b  => sorry
  | .times a b => sorry

def Expr.countNums : Expr → Nat := sorry

/-- `(1 + 2) * 3` -/
def sample : Expr := .times (.plus (.num 1) (.num 2)) (.num 3)
