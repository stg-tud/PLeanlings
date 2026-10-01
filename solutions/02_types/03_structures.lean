/-
# 02.03 — Structures

A `structure` is a product type with *named* fields, like a record or a
class with only public final fields:

    structure Point where
      x : Int
      y : Int

This declares the type `Point`, a constructor `Point.mk : Int → Int → Point`,
and projections `Point.x : Point → Int` and `Point.y : Point → Int`.

Creating values:

    def origin : Point := { x := 0, y := 0 }
    def p : Point := ⟨3, 4⟩            -- anonymous constructor, `\<` `\>`
    def q : Point := Point.mk 3 4      -- the same

Using values: `p.x`, `p.y`. Values are immutable, but you can make a modified
copy: `{ p with x := 10 }` is `p` with its `x` field replaced.

## Your task

1. `Point.add p q` adds two points component-wise.
2. `Point.normSq p` is `x² + y²`.
3. `moveRight p` moves `p` one step to the right (`x` increases by 1), using
   the `with` syntax.

Since `add` and `normSq` are defined in the namespace `Point`, you can use
dot notation: `p.add q`, `p.normSq`.
-/

structure Point where
  x : Int
  y : Int
deriving Repr

def Point.add (p q : Point) : Point := { x := p.x + q.x, y := p.y + q.y }

def Point.normSq (p : Point) : Int := p.x * p.x + p.y * p.y

def moveRight (p : Point) : Point := { p with x := p.x + 1 }

#eval (Point.mk 1 2).add ⟨10, 20⟩
#eval (⟨3, 4⟩ : Point).normSq
#eval moveRight ⟨0, 7⟩
