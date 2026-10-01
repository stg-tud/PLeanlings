/- HINT
For `step`, pattern matching on nested patterns is handy. Put the most
specific pattern first: `| app (lam t) (lam s) => …`, then
`| app (lam t) a => …`, then `| app f a => …`, then `| _ => none`.
`Option.map` turns `step a : Option DTerm` into the stepped application.

For the proofs: the root of `app idt (app idt idt)` is an application of
a value to a non-value, so the rule is `Step.app2`. `Step.beta` needs a
proof of `Value`, which is `Value.lam _`. Lean computes `beta` for you when
checking the type.
-/
open DTerm in
example : step (app (lam (var 1)) (lam (var 0))) = some (var 0) := rfl
open DTerm in
example : step (app (lam (lam (var 1))) (lam (var 0))) = some (lam (lam (var 0))) := rfl
example : step omega = some omega := rfl
example : step idt = none := rfl
open DTerm in
example : step (var 3) = none := rfl
open DTerm in
-- no reduction under binders
example : step (lam (app idt idt)) = none := rfl
open DTerm in
-- stuck: a variable in function position
example : step (app (var 0) idt) = none := rfl
open DTerm in
-- stuck: argument is a variable (not a value)
example : step (app idt (var 0)) = none := rfl
open DTerm in
-- function first ...
example : step (app (app idt idt) (app idt idt)) = some (app idt (app idt idt)) := rfl
open DTerm in
-- ... then the argument
example : step (app idt (app idt idt)) = some (app idt idt) := rfl
open DTerm in
example : step (app (app (var 0) idt) (app idt idt)) = none := rfl
open DTerm in
example : step (app (app (lam (lam (var 1))) idt) omega) =
    some (app (lam idt) omega) := rfl
open DTerm in
example : Step (app idt (app idt idt)) (app idt idt) := step_app2_example
example : Step omega omega := omega_steps_to_itself
-- pin the given definitions
open DTerm in
example : omega = app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0))) := rfl
open DTerm in
example : ∀ f f' a, Step f f' → Step (app f a) (app f' a) := fun _ _ _ h => Step.app1 h
open DTerm in
example : ∀ t, Value (lam t) := Value.lam
