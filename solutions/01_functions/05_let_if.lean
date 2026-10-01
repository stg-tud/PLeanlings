/-
# 01.05 — `let` and `if … then … else`

Inside an expression you can give a name to an intermediate result
with `let`:

    def hypotenuseSq (a b : Nat) : Nat :=
      let a2 := a * a
      let b2 := b * b
      a2 + b2

Each `let` is an *expression*, not a statement: `let x := e; body` means
"`body`, where `x` stands for `e`". There is no mutation; `x` never changes.

Conditionals are expressions too, so `else` is mandatory (what would the
value be otherwise?). Both branches must have the same type:

    def abs (x : Int) : Int := if x < 0 then -x else x

This is like the ternary `c ? a : b` from Java/C, not like an `if`
statement.

## Your task

1. `max3 a b c` returns the largest of three numbers. Use `if` (do not use
   the library function `max`).
2. `collatz n` is `n / 2` if `n` is even, and `3 * n + 1` otherwise.
3. `price` computes the cost of `n` items at 3 each, minus a discount of 5
   if that cost is at least 20. Use `let` to name the cost. (Remember: on
   `Nat`, subtraction never goes below 0.)
-/

def max3 (a b c : Nat) : Nat :=
  if a ≥ b && a ≥ c then a
  else if b ≥ c then b
  else c

def collatz (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

def price (n : Nat) : Nat :=
  let cost := 3 * n
  if cost ≥ 20 then cost - 5 else cost

#eval max3 4 9 2
#eval collatz 7
#eval price 10
