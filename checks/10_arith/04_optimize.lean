/- HINT
Copy the shape of `mkPlus`: one match line per rule, in the given order,
with patterns like `.num 0, _` and `_, .num 1`. The final catch-all line
`| a, b => .times a b` keeps the node unchanged.

`optimize` should first optimize both children and then combine them with
the smart constructor: `mkPlus (optimize a) (optimize b)`.
-/
#guard mkTimes (.num 3) (.num 4) == .num 12
#guard mkTimes (.num 0) (.var "x") == .num 0
#guard mkTimes (.var "x") (.num 0) == .num 0
#guard mkTimes (.num 1) (.var "x") == .var "x"
#guard mkTimes (.var "x") (.num 1) == .var "x"
#guard mkTimes (.var "x") (.var "y") == .times (.var "x") (.var "y")
#guard mkTimes (.num 2) (.var "y") == .times (.num 2) (.var "y")
#guard optimize (.times (.plus (.num 2) (.num 3)) (.var "x")) == .times (.num 5) (.var "x")
#guard optimize (.times (.var "x") (.plus (.num 0) (.num 1))) == .var "x"
#guard optimize (.plus (.var "y") (.times (.num 0) (.var "z"))) == .var "y"
#guard optimize (.plus (.times (.num 2) (.num 3)) (.times (.num 4) (.num 5))) == .num 26
#guard optimize (.plus (.var "a") (.var "b")) == .plus (.var "a") (.var "b")
#guard optimize (.times (.var "a") (.plus (.var "b") (.num 0))) == .times (.var "a") (.var "b")
