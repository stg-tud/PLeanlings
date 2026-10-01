/-
# 10.01 — Abstract syntax trees

Welcome to Part III: programming languages! From now on, the objects we
compute with and reason about are *programs*.

A program is first of all a piece of text, its **concrete syntax**:

    2 + x * 3

A parser turns this text into a tree, the **abstract syntax tree (AST)**:

        plus
       /    \
    num 2   times
           /     \
       var "x"   num 3

The AST forgets everything that only matters for reading and writing text:
whitespace, comments, parentheses, operator precedence. `2 + x * 3`,
`2+(x*3)` and `(2 + (x * (3))) ` all have the *same* AST. Compilers and
interpreters work on ASTs, and so do semantics and type systems.

We will not write parsers in this course. Instead we write ASTs directly,
and in Lean an AST is just an inductive type: one constructor per kind of
node, with the children as arguments.

```
inductive AExp where
  | num   (n : Nat)        -- a literal, e.g. 42
  | var   (x : String)     -- a variable, e.g. x
  | plus  (a b : AExp)     -- a + b
  | times (a b : AExp)     -- a * b
```

This is the grammar

    a ::= n | x | a + a | a * a

written as a Lean type. Note how there is no constructor for parentheses:
the tree structure already says what belongs together.

## Your task

1. Write the ASTs for the concrete expressions given in the comments.
   Mind the usual precedence: `*` binds tighter than `+`.
2. Define `size`, the number of nodes of an AST (every constructor counts 1).
-/

/-! ## Given — do not edit -/

inductive AExp where
  | num   (n : Nat)
  | var   (x : String)
  | plus  (a b : AExp)
  | times (a b : AExp)
  deriving Repr, DecidableEq

-- The example from the explanation: `2 + x * 3`.
def example0 : AExp := .plus (.num 2) (.times (.var "x") (.num 3))

/-! ## Exercises -/

-- `(2 + x) * 3`
def example1 : AExp := .times (.plus (.num 2) (.var "x")) (.num 3)

-- `x * y + 1 + z`     (`+` associates to the left: this is `(x * y + 1) + z`)
def example2 : AExp := .plus (.plus (.times (.var "x") (.var "y")) (.num 1)) (.var "z")

/-- The number of nodes in the tree. -/
def AExp.size : AExp → Nat
  | .num _ => 1
  | .var _ => 1
  | .plus a b => a.size + b.size + 1
  | .times a b => a.size + b.size + 1

#eval example0.size   -- 5
