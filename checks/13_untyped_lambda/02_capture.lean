/- HINT
`subst` is a direct transcription of the five equations; use
`if y = x then … else …` in the `var` and `lam` cases.

For `substChecked`, the only new case is `lam y b` with `y ≠ x`: if `y`
occurs in `fv s` and `x` occurs in `fv b`, return `none`; otherwise recurse
and wrap the result with `lam y` (e.g. `Option.map (lam y)`). For
applications, both recursive calls must succeed (`do`-notation works for
`Option`).
-/
open Term in
example : subst "x" (var "y") (lam "y" (var "x")) = lam "y" (var "y") := by decide
open Term in
example : subst "x" (var "z") (var "x") = var "z" := by decide
open Term in
example : subst "x" (var "z") (var "w") = var "w" := by decide
open Term in
example : subst "x" (var "z") (lam "x" (var "x")) = lam "x" (var "x") := by decide
open Term in
example : subst "x" (var "z") (lam "y" (app (var "x") (var "y"))) =
    lam "y" (app (var "z") (var "y")) := by decide
open Term in
example : subst "x" (lam "a" (var "a")) (app (var "x") (app (var "x") (var "q"))) =
    app (lam "a" (var "a")) (app (lam "a" (var "a")) (var "q")) := by decide
open Term in
example : substChecked "x" (var "y") (lam "y" (var "x")) = none := by decide
open Term in
example : substChecked "x" (var "y") (lam "z" (var "x")) = some (lam "z" (var "y")) := by decide
open Term in
-- `y` is bound, but `x` does not occur below it, so nothing gets captured
example : substChecked "x" (var "y") (lam "y" (var "y")) = some (lam "y" (var "y")) := by decide
open Term in
example : substChecked "x" (var "y") (lam "x" (var "x")) = some (lam "x" (var "x")) := by decide
open Term in
example : substChecked "x" (var "y") (app (var "x") (lam "y" (var "x"))) = none := by decide
open Term in
example : substChecked "x" (var "y") (app (var "x") (lam "w" (var "x"))) =
    some (app (var "y") (lam "w" (var "y"))) := by decide
open Term in
example : substChecked "x" (lam "y" (var "y")) (lam "y" (var "x")) =
    some (lam "y" (lam "y" (var "y"))) := by decide
