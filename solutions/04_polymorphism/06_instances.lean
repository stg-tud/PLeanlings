/-
# 04.06 — Writing and deriving instances

You can make your own types members of a type class by writing an
`instance`:

    inductive Color where
      | red | green | blue

    instance : ToString Color where
      toString c :=
        match c with
        | .red   => "red"
        | .green => "green"
        | .blue  => "blue"

    #eval s!"my favourite color is {Color.red}"

For many classes the instance is so obvious that Lean can write it for you,
with `deriving` after the type definition:

    structure Point where
      x : Int
      y : Int
    deriving Repr, BEq, DecidableEq

* `Repr` lets `#eval` print values,
* `BEq` gives `==` (componentwise / constructor-wise),
* `DecidableEq` makes `p = q` decidable, so `decide` and `if p = q` work.
  We will use this a lot for types in our type checker later.

## Your task

1. `Shape` below has no instances, so the `#eval` and the `example` below
   do not compile. Add a `deriving` clause so that they do.
2. Write a `ToString Suit` instance (the strings are given in the comments).
3. Write an `Add Vec2` instance, so that `+` adds vectors componentwise.
-/

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
deriving Repr, BEq, DecidableEq

#eval Shape.circle 3
example : Shape.circle 3 ≠ Shape.rect 3 3 := by decide
#eval Shape.rect 1 2 == Shape.rect 1 2

inductive Suit where
  | hearts    -- "♥"
  | spades    -- "♠"

instance : ToString Suit where
  toString s :=
    match s with
    | .hearts => "♥"
    | .spades => "♠"

structure Vec2 where
  x : Int
  y : Int
deriving Repr, DecidableEq

instance : Add Vec2 where
  add v w := { x := v.x + w.x, y := v.y + w.y }

#eval s!"{Suit.hearts}{Suit.spades}"
#eval (⟨1, 2⟩ + ⟨10, 20⟩ : Vec2)
