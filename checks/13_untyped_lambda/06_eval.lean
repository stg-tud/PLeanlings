/- HINT
`eval` has two equations, one for `0` fuel and one for `n + 1`; in the
second, `match step t with | some t' => … | none => …`.

For `eval_omega`, use `induction n with | zero => … | succ n ih => …`.
The zero case is `rfl`. In the succ case, first establish
`have h : step omega = some omega := rfl`, then unfold `eval` and rewrite
with `h` (e.g. `simp only [eval, h]`), and finish with `ih`.
-/
open DTerm in
example : eval 0 idt = none := rfl
open DTerm in
example : eval 1 idt = some idt := rfl
open DTerm in
example : eval 1 (app idt idt) = none := rfl
open DTerm in
example : eval 2 (app idt idt) = some idt := rfl
open DTerm in
example : eval 10 (app idt (app idt idt)) = some idt := rfl
open DTerm in
example : eval 10 (app (app K idt) omegaFun) = some idt := rfl
open DTerm in
-- stuck terms are returned as they are
example : eval 10 (app (var 0) idt) = some (app (var 0) idt) := rfl
open DTerm in
example : eval 10 (app idt (app (var 2) idt)) = some (app idt (app (var 2) idt)) := rfl
open DTerm in
-- K ignores its second argument, but CBV still evaluates it: diverges!
example : eval 50 (app (app K idt) omega) = none := rfl
example : eval 50 omega = none := rfl
example : ∀ n, eval n omega = none := eval_omega
example : step omega = some omega := rfl
