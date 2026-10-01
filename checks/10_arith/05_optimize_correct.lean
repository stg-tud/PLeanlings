/- HINT
`eval_mkTimes` works exactly like `eval_mkPlus`: unfold the smart
constructor, split on its match and let `simp_all [eval]` do the rest.

In the induction, the goal for `plus a b` is
`eval env (optimize (.plus a b)) = eval env (.plus a b)`.
Try `simp [optimize, eval_mkPlus, eval, iha, ihb]`.
-/
example : ∀ env a b, eval env (mkTimes a b) = eval env a * eval env b := eval_mkTimes
example : ∀ env e, eval env (optimize e) = eval env e := optimize_correct
example : mkTimes (.num 0) (.var "x") = .num 0 := rfl
example : mkTimes (.num 1) (.var "x") = .var "x" := rfl
example : mkTimes (.var "x") (.num 1) = .var "x" := rfl
example : mkTimes (.var "x") (.var "y") = .times (.var "x") (.var "y") := rfl
example : optimize (.times (.plus (.num 2) (.num 3)) (.var "x")) = .times (.num 5) (.var "x") := rfl
example : optimize (.plus (.var "y") (.times (.num 0) (.var "z"))) = .var "y" := rfl
