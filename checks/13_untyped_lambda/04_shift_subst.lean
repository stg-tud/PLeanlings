/- HINT
Copy the shape of `unshift`: compare `k` with the cutoff `c` in the `var`
case, increase the cutoff under `lam`, and recurse in `app`.

For `subst`, under `lam t` you are looking for `j + 1` and must insert
`shift 1 0 s` instead of `s`.
-/
open DTerm in
example : shift 1 0 (var 0) = var 1 := rfl
open DTerm in
example : shift 3 0 (var 2) = var 5 := rfl
open DTerm in
example : shift 1 1 (var 0) = var 0 := rfl
open DTerm in
example : shift 2 1 (var 1) = var 3 := rfl
open DTerm in
example : shift 0 0 (app (var 4) (var 7)) = app (var 4) (var 7) := rfl
open DTerm in
-- shifting under binders: bound indices stay, free ones move
example : shift 1 0 (lam (app (var 0) (var 1))) = lam (app (var 0) (var 2)) := rfl
open DTerm in
example : shift 2 0 (lam (lam (app (var 1) (app (var 0) (var 2))))) =
    lam (lam (app (var 1) (app (var 0) (var 4)))) := rfl
open DTerm in
example : shift 1 1 (app (var 0) (lam (app (var 0) (app (var 1) (var 2))))) =
    app (var 0) (lam (app (var 0) (app (var 1) (var 3)))) := rfl
open DTerm in
-- closed terms are unaffected
example : shift 5 0 (lam (lam (var 1))) = lam (lam (var 1)) := rfl
open DTerm in
example : subst 0 (var 7) (var 0) = var 7 := rfl
open DTerm in
example : subst 0 (var 7) (var 1) = var 1 := rfl
open DTerm in
example : subst 2 (lam (var 0)) (app (var 2) (var 1)) = app (lam (var 0)) (var 1) := rfl
open DTerm in
-- under a binder we look for index j+1 ...
example : subst 0 (lam (var 0)) (lam (app (var 0) (var 1))) = lam (app (var 0) (lam (var 0))) := rfl
open DTerm in
-- ... and shift the substituted term
example : subst 0 (var 0) (lam (var 1)) = lam (var 1) := rfl
open DTerm in
example : subst 0 (var 3) (lam (lam (app (var 2) (var 0)))) = lam (lam (app (var 5) (var 0))) := rfl
open DTerm in
example : subst 1 (app (var 0) (var 1)) (lam (app (var 2) (var 1))) =
    lam (app (app (var 1) (var 2)) (var 1)) := rfl
open DTerm in
example : subst 0 (lam (app (var 0) (var 1))) (lam (var 1)) = lam (lam (app (var 0) (var 2))) := rfl
-- β-reduction, end to end
open DTerm in
example : beta (lam (var 1)) (lam (var 0)) = lam (lam (var 0)) := rfl
open DTerm in
example : beta (var 0) (var 3) = var 3 := rfl
open DTerm in
example : beta (var 1) (lam (var 0)) = var 0 := rfl
open DTerm in
example : beta (app (var 0) (var 0)) (lam (app (var 0) (var 0))) =
    app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0))) := rfl
open DTerm in
example : beta (lam (app (var 1) (var 2))) (var 0) = lam (app (var 1) (var 1)) := rfl
open DTerm in
example : unshift 0 (lam (app (var 0) (var 2))) = lam (app (var 0) (var 1)) := rfl
