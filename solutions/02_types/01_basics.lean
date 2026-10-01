/-
# 02.01 — Basic types

Lean has the usual basic types:

| type     | values                      | notes                                  |
|----------|-----------------------------|----------------------------------------|
| `Nat`    | `0`, `1`, `2`, …            | natural numbers, *no upper bound*      |
| `Int`    | `-3`, `0`, `7`, …           | integers                               |
| `Bool`   | `true`, `false`             | `&&`, `||`, `!`                        |
| `String` | `"hello"`                   | `++` concatenates, `.length`           |
| `Char`   | `'a'`, `'Z'`                | single characters, single quotes       |

Two surprises for newcomers:

* `Nat` subtraction is **truncated**: `3 - 5 = 0`, because there is no
  negative natural number. Use `Int` if you need negatives:
  `(3 : Int) - 5 = -2`. The `(e : T)` syntax is a *type ascription*.
* `Nat` division rounds down: `7 / 2 = 3`, and `7 / 0 = 0` (no exception!).

Many functions live in the *namespace* of their type and can be called with
dot notation: `"abc".length` means `String.length "abc"`, and
`'a'.isUpper` means `Char.isUpper 'a'`.

## Your task

1. Replace the `sorry`s in `natDiff`, `intDiff` and `natQuot` by the
   *literal values* that the expressions in the comments evaluate to.
   Predict them first, then check with `#eval`.
2. Define `shout s`, which appends `"!"` to `s`.
3. Define `isDigitOrSpace c`, which is `true` iff the character `c` is a
   digit (`Char.isDigit`) or the space character `' '`.
-/

def natDiff : Nat := 0     -- the value of `(3 : Nat) - 5`
def intDiff : Int := -2    -- the value of `(3 : Int) - 5`
def natQuot : Nat := 3     -- the value of `(7 : Nat) / 2`

def shout (s : String) : String := s ++ "!"

def isDigitOrSpace (c : Char) : Bool := c.isDigit || c == ' '

#eval shout "hello"
#eval "Lean".length
#eval isDigitOrSpace '7'
