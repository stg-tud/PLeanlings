/-
# 01.02 — Anonymous functions

Functions in Lean are values, just like numbers. You can write a function
*without giving it a name*, using `fun`:

    fun x => x + 1             -- the function that adds one
    fun (x : Nat) => x + 1     -- the same, with the type written out
    fun x y => x * y           -- two arguments

    #eval (fun x => x + 1) 41  -- 42

This is exactly the notation of the **lambda calculus**: `fun x => t` is
what textbooks write as `λx. t`. (Lean even accepts `λ x => t`.) Keep this
in mind: at the end of the course you will implement the simply typed lambda
calculus *in* Lean, and its terms look just like this.

A named definition is just a name for a lambda. These two are the same:

    def inc (x : Nat) : Nat := x + 1
    def inc' : Nat → Nat := fun x => x + 1

There is also a short form `(· + 1)`: each `·` becomes an argument.

## Your task

Define the following functions **using `fun`** (the type is given after the
colon, so the definition has no named arguments):

1. `triple`, which multiplies its argument by 3.
2. `between`, which checks `lo ≤ x ∧ x ≤ hi` for arguments `lo`, `hi`, `x`
   (in this order). A comparison like `lo ≤ x` can be used directly as a
   `Bool`, and `&&` is boolean "and".
-/

def triple : Nat → Nat := sorry

def between : Nat → Nat → Nat → Bool := sorry
