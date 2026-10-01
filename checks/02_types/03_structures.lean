/- HINT
Build a point with `{ x := …, y := … }` and access fields with `p.x`.

For `moveRight`, `{ p with x := … }` keeps `y` and only changes `x`.
-/
example : Point → Point → Point := Point.add
example : Point → Int := Point.normSq
example : Point → Point := moveRight
example : (Point.mk 1 2).add ⟨10, 20⟩ = ⟨11, 22⟩ := rfl
example : (Point.mk (-1) 5).add ⟨1, -7⟩ = ⟨0, -2⟩ := rfl
example : (Point.mk 3 4).normSq = 25 := rfl
example : (Point.mk (-2) 0).normSq = 4 := rfl
example : (Point.mk 0 0).normSq = 0 := rfl
example : moveRight ⟨0, 7⟩ = ⟨1, 7⟩ := rfl
example : moveRight ⟨-1, -1⟩ = ⟨0, -1⟩ := rfl
