/- HINT
A variable is looked up in the environment: `env x`. The compound cases call
`eval env` recursively on both children and combine the results with Lean's
`+` and `*`.

For the proofs: `simp [eval]` rewrites with the defining equations of
`eval`. For commutativity of multiplication, give simp the lemma as well:
`simp [eval, Nat.mul_comm]`.
-/
example : eval Env.empty (.num 3) = 3 := rfl
example : eval (Env.empty.set "x" 5) (.var "x") = 5 := rfl
example : eval (Env.empty.set "x" 5) (.var "y") = 0 := rfl
example : eval (Env.empty.set "x" 5) (.plus (.num 2) (.times (.var "x") (.num 3))) = 17 := rfl
example : eval ((Env.empty.set "x" 5).set "y" 4) (.times (.plus (.var "y") (.num 1)) (.var "x")) = 25 := rfl
example : ∀ env a, eval env (.plus a (.num 0)) = eval env a := eval_plus_zero
example : ∀ env a b, eval env (.times a b) = eval env (.times b a) := eval_times_comm
