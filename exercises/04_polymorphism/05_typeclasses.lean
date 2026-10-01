/-
# 04.05 — Type classes

Can we write a polymorphic `contains x xs`? We need to compare elements,
but not every type has a sensible equality test (think of functions).
**Type classes** solve this: a class describes an operation that *some*
types support, and a function can require it with an argument in square
brackets:

    def contains {α : Type} [BEq α] (x : α) : List α → Bool
      | []      => false
      | y :: ys => x == y || contains x ys

`[BEq α]` means "α must have a `==` operation". When you call
`contains 3 [1, 2, 3]`, Lean finds the **instance** `BEq Nat` automatically.
This is like interfaces in Java or traits in Rust.

Some classes you will meet a lot:

| class          | provides                    | used by            |
|----------------|-----------------------------|--------------------|
| `BEq α`        | `a == b : Bool`             |                    |
| `ToString α`   | `toString a : String`       | `s!"…{a}…"`        |
| `Repr α`       | a representation of values  | `#eval`            |
| `Add α`, `Mul α` | `a + b`, `a * b`          |                    |
| `DecidableEq α` | decidable `a = b`          | `if a = b`, `decide` |

In fact, `+` is not built in at all: `a + b` means `Add.add a b`, for
whichever type has an `Add` instance.

## Your task

1. Implement `count x xs`, the number of times `x` occurs in `xs`. Add the
   class argument it needs.
2. Implement `showAll xs`, which converts all elements to strings and
   puts `", "` between them: `showAll [1, 2, 3] = "1, 2, 3"`.
   (Match on `[]`, `[x]`, and `x :: xs`.)
-/

def contains {α : Type} [BEq α] (x : α) : List α → Bool
  | []      => false
  | y :: ys => x == y || contains x ys

def count {α : Type} (x : α) : List α → Nat := sorry

def showAll {α : Type} [ToString α] : List α → String
  | []      => sorry
  | [x]     => sorry
  | x :: xs => sorry

#eval contains "b" ["a", "b"]
