/-
# 01.04 — Higher-order functions

Since functions are values, they can be *arguments* to other functions.
A function that takes (or returns) a function is called **higher-order**.

    def applyTo5 (f : Nat → Nat) : Nat := f 5
    #eval applyTo5 (fun x => x * 10)       -- 50

Note the parentheses in `(f : Nat → Nat)`: the argument `f` itself has a
function type.

## Your task

1. `twice f x` applies `f` two times to `x`, i.e. computes `f (f x)`.
2. `compose g f` is the function that first applies `f`, then `g`
   ("`g` after `f`"). It *returns a function*, so its body can be a `fun`.
   (Lean's built-in version is written `g ∘ f`.)
3. `fourTimes f` applies `f` four times. Define it using `twice` (and
   without writing `f (f (f (f …)))`).
-/

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def compose (g : Nat → Nat) (f : Nat → Nat) : Nat → Nat := fun x => g (f x)

def fourTimes (f : Nat → Nat) : Nat → Nat := twice (twice f)

#eval twice (· + 3) 10                  -- 16
#eval compose (· * 2) (· + 1) 5         -- 12
#eval fourTimes (· * 2) 1               -- 16
