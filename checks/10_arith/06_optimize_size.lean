/- HINT
For the lemmas: `unfold mkPlus`, then `split <;> simp [AExp.size] <;> omega`.

For the induction step `plus a b`: first
`have h := size_mkPlus (optimize a) (optimize b)`, then
`simp [optimize, AExp.size]` and finally `omega`, which combines `h`, `iha`
and `ihb`.
-/
example : ∀ a b, (mkPlus a b).size ≤ a.size + b.size + 1 := size_mkPlus
example : ∀ a b, (mkTimes a b).size ≤ a.size + b.size + 1 := size_mkTimes
example : ∀ e, (optimize e).size ≤ e.size := size_optimize
example : (AExp.plus (.num 1) (.var "x")).size = 3 := rfl
example : optimize (.times (.var "x") (.plus (.num 0) (.num 1))) = .var "x" := rfl
example : mkPlus (.var "x") (.var "y") = .plus (.var "x") (.var "y") := rfl
example : mkTimes (.var "x") (.var "y") = .times (.var "x") (.var "y") := rfl
