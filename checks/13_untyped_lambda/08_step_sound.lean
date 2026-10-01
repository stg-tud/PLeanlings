/- HINT
`value_no_step`: `cases` on the `Value` proof leaves only `v = lam t`, and
`step (lam t) = none` holds by `rfl`.

`step_sound`: start with `intro t` and `induction t`, keeping `t'`
universally quantified (intro it inside each case). In the `app f a` case
do `cases f` and, in the `lam` subcase, `cases a`. After
`simp [step] at h`, either the goal is closed, or `h` is an equation
`beta … = t'` (use `subst h` then `Step.beta`), or an existential to
`obtain ⟨_, _, rfl⟩ := h` and finish with `Step.app1`/`Step.app2` and the
induction hypothesis.
-/
example : ∀ v, Value v → step v = none := value_no_step
example : ∀ t t', step t = some t' → Step t t' := step_sound
-- pin the given definitions
open DTerm in
example : ∀ t, Value (lam t) := Value.lam
open DTerm in
example : ∀ f f' a, Step f f' → Step (app f a) (app f' a) := fun _ _ _ h => Step.app1 h
open DTerm in
example : ∀ v a a', Value v → Step a a' → Step (app v a) (app v a') := fun _ _ _ h1 h2 => Step.app2 h1 h2
open DTerm in
example : ∀ t v, Value v → Step (app (lam t) v) (beta t v) := fun _ _ h => Step.beta h
open DTerm in
example : step (app (app (lam (lam (var 1))) (lam (var 0))) (app (lam (var 0)) (lam (var 0)))) =
    some (app (lam (lam (var 0))) (app (lam (var 0)) (lam (var 0)))) := rfl
open DTerm in
example : step (app (lam (var 0)) (app (lam (var 0)) (lam (var 0)))) =
    some (app (lam (var 0)) (lam (var 0))) := rfl
open DTerm in
example : step (app (var 0) (lam (var 0))) = none := rfl
open DTerm in
example : beta (lam (app (var 1) (var 2))) (var 0) = lam (app (var 1) (var 1)) := rfl
