/-
# 03.02 — Recursive types: natural numbers

Constructors may take arguments, including values of the type being
defined. This is how Lean's own `Nat` is defined:

    inductive Nat where
      | zero : Nat
      | succ (n : Nat) : Nat      -- "successor", i.e. n + 1

So `3` is really `succ (succ (succ zero))`. Below we build our own copy,
`MyNat`, to see how this works.

Functions on recursive types are usually **recursive**, following the
structure of the type: one case for `zero`, and one case for `succ n` that
may call the function on the smaller `n`.

    def MyNat.double : MyNat → MyNat
      | .zero   => .zero
      | .succ n => .succ (.succ (double n))

This is called **structural recursion**: each recursive call is on a direct
sub-part of the input, so it obviously terminates.

## Your task

1. `MyNat.add m n`: recurse on `n`. (`m + 0 = m` and `m + (n+1) = (m+n) + 1`.)
2. `MyNat.mul m n`: recurse on `n`, using `add`.
   (`m * 0 = 0` and `m * (n+1) = m * n + m`.)
-/

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
deriving Repr

/-- Convert to Lean's `Nat`, so we can look at results with `#eval`. -/
def MyNat.toNat : MyNat → Nat
  | .zero   => 0
  | .succ n => n.toNat + 1

/-- Convert from Lean's `Nat`. -/
def MyNat.ofNat : Nat → MyNat
  | 0     => .zero
  | n + 1 => .succ (ofNat n)

def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (double n))

#eval (MyNat.double (MyNat.ofNat 21)).toNat   -- 42

def MyNat.add (m : MyNat) : MyNat → MyNat
  | .zero   => sorry
  | .succ n => sorry

def MyNat.mul (m : MyNat) : MyNat → MyNat
  | .zero   => sorry
  | .succ n => sorry
