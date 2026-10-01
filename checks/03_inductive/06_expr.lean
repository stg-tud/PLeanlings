/- HINT
One case per constructor. A literal evaluates to its number; for `plus`
and `times`, evaluate both sub-expressions recursively and combine them.

`countNums` has the same shape, but a literal counts as `1`.
-/
example : Expr → Nat := Expr.eval
example : Expr → Nat := Expr.countNums
example : sample = .times (.plus (.num 1) (.num 2)) (.num 3) := rfl
example : (Expr.num 5).eval = 5 := rfl
example : sample.eval = 9 := rfl
example : (Expr.plus (.num 2) (.times (.num 3) (.num 4))).eval = 14 := rfl
example : (Expr.times (.num 0) (.plus (.num 3) (.num 4))).eval = 0 := rfl
example : (Expr.times (.num 2) (.num 1)).eval = 2 := rfl
example : (Expr.num 5).countNums = 1 := rfl
example : sample.countNums = 3 := rfl
example : (Expr.plus (.plus (.num 1) (.num 1)) (.times (.num 1) (.num 1))).countNums = 4 := rfl
