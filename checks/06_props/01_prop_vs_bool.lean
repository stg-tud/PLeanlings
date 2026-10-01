/- HINT
Equations whose sides compute to the same value can be proved with `rfl`.
For `<` use `by decide`.

`isSmall 3 = true` is an equation too, so `rfl` works there as well as `by decide`.
-/
example : isSmall 3 = true := rfl
example : isSmall 7 = false := rfl
example : 2 + 2 = 4 := two_plus_two
example : [1, 2] ++ [3] = [1, 2, 3] := append_example
example : 3 * 7 < 22 := lt_example
example : isSmall 3 = true := small_three
