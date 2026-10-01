/-
# 04.04 — `foldr`: the mother of all list functions

Many list functions have the same shape: a result for `[]`, and a way to
combine the head with the result for the tail. `foldr` captures this shape
once and for all:

    foldr f init [a, b, c]  =  f a (f b (f c init))

Think of it as replacing every `::` by `f` and the final `[]` by `init`:

    [a, b, c]  =  a :: (b :: (c :: []))
    foldr f i  =  a `f` (b `f` (c `f` i))

For example, `foldr (· + ·) 0 xs` is the sum of `xs`, because `·+·` is
`fun a b => a + b`. (Library: `List.foldr`.)

## Your task

1. Implement `foldr`.
2. Define `sum`, `all`, and `concat` using `foldr` (no explicit recursion!).
   * `all p xs` is `true` iff `p x` holds for every element.
   * `concat` flattens a list of lists: `concat [[1], [2, 3]] = [1, 2, 3]`.
-/

def foldr {α β : Type} (f : α → β → β) (init : β) : List α → β
  | []      => init
  | x :: xs => f x (foldr f init xs)

def sum (xs : List Nat) : Nat := foldr (· + ·) 0 xs

def all {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  foldr (fun x acc => p x && acc) true xs

def concat {α : Type} (xss : List (List α)) : List α := foldr (· ++ ·) [] xss

#eval foldr (fun x acc => s!"({x} {acc})") "nil" [1, 2, 3]
#eval sum [1, 2, 3, 4]
#eval all (· > 0) [1, 2, 3]
#eval concat [[1], [2, 3], []]
