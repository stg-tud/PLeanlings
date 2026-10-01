/- HINT
Build the tree from the root down: the root is the operator that is applied
*last*. In `(2 + x) * 3` that is the `*`, so `example1` starts with `.times`.

For `size`, a `plus` node counts itself (1) plus all nodes of both subtrees:
`a.size + b.size + 1`.
-/
example : example1 = .times (.plus (.num 2) (.var "x")) (.num 3) := by decide
example : example2 = .plus (.plus (.times (.var "x") (.var "y")) (.num 1)) (.var "z") := by decide
example : example0.size = 5 := by decide
example : (AExp.var "y").size = 1 := by decide
example : example2.size = 7 := by decide
example : (AExp.times (.num 1) (.plus (.var "a") (.num 2))).size = 5 := by decide
