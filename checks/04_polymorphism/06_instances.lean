/- HINT
`deriving` goes on its own line directly after the constructors, and takes
a comma-separated list of class names. Which classes do `#eval`, `decide`,
and `==` need?

An instance is written like a structure: `instance : Add Vec2 where`
followed by `add v w := …` on the next line.
-/
example : Shape.circle 1 ≠ Shape.circle 2 := by decide
example : Shape.rect 1 2 = Shape.rect 1 2 := by decide
#guard Shape.rect 1 2 == Shape.rect 1 2
#guard (Shape.rect 1 2 == Shape.rect 2 1) = false
#guard toString Suit.hearts = "♥"
#guard toString Suit.spades = "♠"
#guard s!"{Suit.spades}{Suit.hearts}" = "♠♥"
example : (⟨1, 2⟩ + ⟨10, 20⟩ : Vec2) = ⟨11, 22⟩ := by decide
example : (⟨-1, 0⟩ + ⟨1, 5⟩ : Vec2) = ⟨0, 5⟩ := by decide
example : (⟨3, 4⟩ + ⟨0, 0⟩ : Vec2) = ⟨3, 4⟩ := by decide
