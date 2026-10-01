/-
# 03.03 — Lists

A list of numbers is either empty, or a first element (the *head*) followed
by another list (the *tail*):

    inductive NatList where
      | nil  : NatList
      | cons (head : Nat) (tail : NatList) : NatList

So `[1, 2]` corresponds to `cons 1 (cons 2 nil)`. This is a *linked list*.
Lean's built-in `List` is defined in exactly this way (but works for any
element type; see chapter 04). There, `nil` is written `[]` and `cons x xs`
is written `x :: xs`.

Recursive functions again follow the shape of the type:

    def NatList.sum : NatList → Nat
      | .nil       => 0
      | .cons x xs => x + xs.sum

## Your task

1. `NatList.length xs`: the number of elements.
2. `NatList.append xs ys`: all elements of `xs`, followed by those of `ys`.
   Recurse on `xs`.
3. `NatList.reverse xs`: the elements in reverse order. Use `append`.
-/

inductive NatList where
  | nil  : NatList
  | cons (head : Nat) (tail : NatList) : NatList
deriving Repr

/-- Convert to Lean's `List Nat`, so we can look at results. -/
def NatList.toList : NatList → List Nat
  | .nil       => []
  | .cons x xs => x :: xs.toList

/-- Convert from Lean's `List Nat`. -/
def NatList.ofList : List Nat → NatList
  | []      => .nil
  | x :: xs => .cons x (ofList xs)

def NatList.sum : NatList → Nat
  | .nil       => 0
  | .cons x xs => x + xs.sum

def NatList.length : NatList → Nat
  | .nil       => 0
  | .cons _ xs => xs.length + 1

def NatList.append : NatList → NatList → NatList
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

def NatList.reverse : NatList → NatList
  | .nil       => .nil
  | .cons x xs => xs.reverse.append (.cons x .nil)

#eval (NatList.ofList [1, 2, 3]).length
#eval ((NatList.ofList [1, 2]).append (NatList.ofList [3, 4])).toList
#eval (NatList.ofList [1, 2, 3]).reverse.toList
