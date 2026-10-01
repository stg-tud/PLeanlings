/- HINT
For each variable, count the `λ`s between it and its binder: in
`λx. λy. λz. x z (y z)` the variable `z` is `0`, `y` is `1`, `x` is `2`.

For `toDB`: in the `var` case look the name up with `indexOf x Γ` and wrap
the result with `.var`; in the `lam x b` case recurse with `x :: Γ` and wrap
with `.lam`; in the `app` case both sides must succeed.
-/
example : K_db = .lam (.lam (.var 1)) := rfl
example : S_db = .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))) := rfl
example : omega_db = .lam (.app (.var 0) (.var 0)) := rfl
example : toDB [] (.lam "x" (.lam "y" (.var "x"))) = some K_db := by decide
example : toDB [] (.lam "x" (.lam "y" (.lam "z"
    (.app (.app (.var "x") (.var "z")) (.app (.var "y") (.var "z")))))) = some S_db := by decide
example : toDB [] (.lam "x" (.app (.var "x") (.var "x"))) = some omega_db := by decide
-- α-equivalent terms become equal
example : toDB [] (.lam "x" (.var "x")) = toDB [] (.lam "y" (.var "y")) := by decide
example : toDB [] (.lam "a" (.lam "b" (.var "a"))) = some K_db := by decide
-- shadowing: the innermost binder wins
example : toDB [] (.lam "x" (.lam "x" (.var "x"))) = some (.lam (.lam (.var 0))) := by decide
-- the same variable gets different indices at different depths
example : toDB [] (.lam "x" (.app (.var "x") (.lam "y" (.app (.var "x") (.var "y"))))) =
    some (.lam (.app (.var 0) (.lam (.app (.var 1) (.var 0))))) := by decide
-- free variables
example : toDB [] (.var "x") = none := by decide
example : toDB [] (.lam "x" (.app (.var "x") (.var "y"))) = none := by decide
example : toDB ["y"] (.lam "x" (.app (.var "x") (.var "y"))) = some (.lam (.app (.var 0) (.var 1))) := by decide
example : toDB ["a", "b", "c"] (.var "c") = some (.var 2) := by decide
example : toDB ["a"] (.app (.var "a") (.var "a")) = some (.app (.var 0) (.var 0)) := by decide
