/-
# 02.04 — `Option`: values that might be missing

What should `10 / 0` be? What is the first element of an empty list?
Java returns `null` or throws; Lean has no `null`. Instead, the type
`Option α` has two kinds of values:

* `none` — no value,
* `some a` — a value `a : α`.

The type tells you (and forces you!) to handle the missing case.
To use an `Option`, pattern match on it:

    def orZero (o : Option Nat) : Nat :=
      match o with
      | none   => 0
      | some n => n

(The library has this as `o.getD 0`, "get with default".)

Lists are written `[1, 2, 3]`, and patterns `[]` and `x :: xs`
match the empty list and a list with head `x` and tail `xs`.

## Your task

1. `safeDiv n k` returns `none` when `k = 0` and `some (n / k)` otherwise.
2. `head? xs` returns the first element of `xs`, if there is one.
3. `addOpt a b` adds two optional numbers; the result is `none` if either
   input is `none`.
-/

def safeDiv (n k : Nat) : Option Nat :=
  if k == 0 then none else some (n / k)

def head? (xs : List Nat) : Option Nat :=
  match xs with
  | []     => none
  | x :: _ => some x

def addOpt (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (x + y)
  | _, _           => none

#eval safeDiv 10 2
#eval safeDiv 10 0
#eval head? [3, 1, 4]
#eval addOpt (some 1) none
