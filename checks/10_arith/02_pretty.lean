/- HINT
For `toStr`, mirror the shape `"(" ++ left ++ " + " ++ right ++ ")"`, using
recursive calls `a.toStr` and `b.toStr`.

For `prettyAt`, the `plus` case is
`parenIf (ctx > 1) (a.prettyAt 1 ++ " + " ++ b.prettyAt 2)`. The `times`
case is analogous, with levels 2 and 3 and condition `ctx > 2`.
-/
#guard (AExp.plus (.num 2) (.times (.var "x") (.num 3))).toStr == "(2 + (x * 3))"
#guard (AExp.times (.plus (.num 2) (.var "x")) (.num 3)).toStr == "((2 + x) * 3)"
#guard (AExp.plus (.num 2) (.times (.var "x") (.num 3))).pretty == "2 + x * 3"
#guard (AExp.times (.plus (.num 2) (.var "x")) (.num 3)).pretty == "(2 + x) * 3"
#guard (AExp.plus (.plus (.times (.var "x") (.var "y")) (.num 1)) (.var "z")).pretty == "x * y + 1 + z"
#guard (AExp.plus (.var "a") (.plus (.var "b") (.var "c"))).pretty == "a + (b + c)"
#guard (AExp.times (.var "a") (.times (.var "b") (.var "c"))).pretty == "a * (b * c)"
#guard (AExp.times (.times (.var "a") (.var "b")) (.var "c")).pretty == "a * b * c"
#guard (AExp.times (.var "a") (.plus (.var "b") (.num 10))).pretty == "a * (b + 10)"
#guard (AExp.num 7).pretty == "7"
