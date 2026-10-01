/-
# 01.01 — Defining functions

A function definition in Lean looks like this:

    def double (n : Nat) : Nat := n + n

Read it as: "`double` takes an argument `n` of type `Nat` and returns a `Nat`,
namely `n + n`". Compared to Java or Python:

* there is no `return`: the body after `:=` *is* the result,
* the argument types and the result type are written after a colon,
* function **application** uses a space, not parentheses: `double 5`,
  not `double(5)`. Parentheses only group: `double (double 5)`.

Several arguments are just listed one after another:

    def add (a : Nat) (b : Nat) : Nat := a + b
    def add' (a b : Nat) : Nat := a + b    -- same thing, shorter

    #eval add 2 3                          -- 5

## Your task

1. Define `square n` as `n` times `n`.
2. Define `sumOfSquares a b` as `a² + b²`, **using** `square`.
3. Define `isEven n`, returning `true` exactly when `n` is even.
   The remainder operator is `%`, and `==` compares two values and returns a
   `Bool`.
-/

def double (n : Nat) : Nat := n + n

#eval double 21

def square (n : Nat) : Nat := sorry

def sumOfSquares (a b : Nat) : Nat := sorry

def isEven (n : Nat) : Bool := sorry
