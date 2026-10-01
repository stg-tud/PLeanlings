/- HINT
Translate the named versions. Under `λb.` the variable `b` is `0`; under
`λb. λc.` it is `1` and `c` is `0`. Closed terms like `fls` and `tru` can be
used inside other terms without any shifting.

For `plus = λm. λn. λf. λx. m f (n f x)`: below four binders, `m` is `3`,
`n` is `2`, `f` is `1` and `x` is `0`.
-/
open DTerm in
example : norm 100 fls = some (lam (lam (var 0))) := by decide
open DTerm in
example : norm 100 (app not tru) = some (lam (lam (var 0))) := by decide
open DTerm in
example : norm 100 (app not fls) = some tru := by decide
open DTerm in
example : norm 100 (app (app and tru) tru) = some tru := by decide
open DTerm in
example : norm 100 (app (app and tru) fls) = norm 100 fls := by decide
open DTerm in
example : norm 100 (app (app and fls) tru) = norm 100 fls := by decide
open DTerm in
example : norm 100 (app (app and fls) fls) = norm 100 fls := by decide
open DTerm in
example : norm 100 (app not (app (app and tru) (app not fls))) = norm 100 fls := by decide
open DTerm in
example : norm 200 (app (app plus (numeral 0)) (numeral 0)) = some (numeral 0) := by decide
open DTerm in
example : norm 200 (app (app plus (numeral 1)) (numeral 2)) = some (numeral 3) := by decide
open DTerm in
example : norm 200 (app (app plus (numeral 2)) (numeral 0)) = some (numeral 2) := by decide
open DTerm in
example : norm 200 (app (app plus (numeral 0)) (numeral 3)) = some (numeral 3) := by decide
open DTerm in
example : norm 300 (app (app plus (numeral 3)) (numeral 4)) = some (numeral 7) := by decide
open DTerm in
example : norm 300 (app (app plus (app succ (numeral 1))) (app (app plus (numeral 1)) (numeral 1))) =
    some (numeral 4) := by decide
-- pin the given definitions
open DTerm in
example : tru = lam (lam (var 1)) := rfl
open DTerm in
example : numeral 2 = lam (lam (app (var 1) (app (var 1) (var 0)))) := rfl
open DTerm in
example : norm 100 (app succ (numeral 2)) = some (numeral 3) := by decide
