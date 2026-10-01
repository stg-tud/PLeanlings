/- HINT
Build terms from the inside out. `λx. λy. x` is
`lam "x" (lam "y" (var "x"))`. For `S`, the body `x z (y z)` is an
application of `x z` to `y z`.

For `fv`: a variable contributes itself, a lambda removes its parameter from
the free variables of the body (`(fv b).filter (· != x)`), and an
application concatenates.
-/
example : K = .lam "x" (.lam "y" (.var "x")) := rfl
example : S = .lam "x" (.lam "y" (.lam "z"
    (.app (.app (.var "x") (.var "z")) (.app (.var "y") (.var "z"))))) := rfl
example : omega = .lam "x" (.app (.var "x") (.var "x")) := rfl
example : I = .lam "x" (.var "x") := rfl
example : fv (.var "a") = ["a"] := by decide
example : fv I = [] := by decide
example : fv K = [] := by decide
example : fv S = [] := by decide
example : fv omega = [] := by decide
example : fv (.lam "x" (.app (.var "x") (.var "y"))) = ["y"] := by decide
example : fv (.app (.var "y") (.lam "y" (.var "y"))) = ["y"] := by decide
example : fv (.app (.var "a") (.app (.var "b") (.var "a"))) = ["a", "b", "a"] := by decide
example : fv (.lam "x" (.lam "y" (.app (.var "z") (.app (.var "x") (.var "w"))))) = ["z", "w"] := by decide
example : fv (.lam "x" (.app (.var "x") (.var "x"))) = [] := by decide
example : closed S = true := by decide
example : closed (.lam "x" (.var "y")) = false := by decide
