/-
# 05.02 — Errors with messages: `Except`

`Option` tells you *that* something failed, but not *why*. The type
`Except ε α` is like `Option α`, but a failure carries an error value of
type `ε`, typically a `String` message:

* `Except.ok a` — success with result `a`,
* `Except.error e` — failure with error `e`.

`Except ε` is a monad too, so `do`, `←`, and `pure` work exactly as for
`Option`. To fail, write `throw e` (which is `Except.error e`):

    def checkPositive (n : Int) : Except String Int :=
      if n > 0 then pure n else throw s!"{n} is not positive"

`s!"…{e}…"` is string interpolation: `{e}` is replaced by `toString e`.
A `throw` stops the whole `do` block, like an exception, and the first error
is the result.

You will use `Except String` a lot later: a type checker either returns a
type or an error message explaining why the program is ill-typed.

To *handle* the result, pattern match:

    match checkPositive (-3) with
    | .ok n    => …
    | .error e => …

## Your task

1. `safeDiv n k` fails with exactly the message `"division by zero"` if
   `k = 0`.
2. `digit c` converts a character `'0'`…`'9'` to its value (use
   `c.toNat - '0'.toNat`), and otherwise fails with the message
   `s!"not a digit: {c}"`.
3. `twoDigits s` converts a two-character string such as `"42"` into the
   number 42, using `digit` for both characters. If `s` does not have
   exactly two characters, fail with `"expected two digits"`.
   `s.toList` gives the list of characters.
4. `orDefault r d` returns the result of `r`, or `d` if `r` failed.
-/

def safeDiv (n k : Nat) : Except String Nat :=
  if k == 0 then throw "division by zero" else pure (n / k)

def digit (c : Char) : Except String Nat :=
  if c.isDigit then pure (c.toNat - '0'.toNat) else throw s!"not a digit: {c}"

def twoDigits (s : String) : Except String Nat :=
  match s.toList with
  | [c1, c2] => do
    let d1 ← digit c1
    let d2 ← digit c2
    pure (10 * d1 + d2)
  | _ => throw "expected two digits"

def orDefault (r : Except String Nat) (d : Nat) : Nat :=
  match r with
  | .ok n    => n
  | .error _ => d

#eval safeDiv 7 0
#eval twoDigits "42"
#eval twoDigits "4x"
#eval orDefault (twoDigits "?") 0
