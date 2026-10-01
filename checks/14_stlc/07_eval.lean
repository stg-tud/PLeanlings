/- HINT
For `step (.app f a)`, use nested `if isValue f then … else …` as described,
and in the β case `match f with | .lam _ t => some (subst (subst1 a) t) | _ => none`.
Look at the `pred` case for inspiration.

`eval` is defined by pattern matching on the fuel: `| 0, t => t` and
`| n + 1, t => match step t with …`.
-/
-- The step function must compute as before.
example : step (.app (.lam .nat (.succ (.var 0))) .zero) = some (.succ .zero) := rfl
example : step (.app (.lam .nat (.var 0)) (.pred .zero)) = some (.app (.lam .nat (.var 0)) .zero) := rfl
example : step (.app (.app (.lam .bool (.lam .nat (.var 1))) .tru) .zero) = some (.app (.lam .nat .tru) .zero) := rfl
example : step (.app .tru .zero) = none := rfl
example : step (.ite .tru .zero .fls) = some .zero := rfl
example : step (.ite (.iszero .zero) .zero .fls) = some (.ite .tru .zero .fls) := rfl
example : step (.pred (.succ .zero)) = some .zero := rfl
example : step (.iszero (.succ .zero)) = some .fls := rfl
example : step (.succ (.pred .zero)) = some (.succ .zero) := rfl
example : step (.lam .nat (.pred .zero)) = none := rfl
example : isValue (.succ (.succ .zero)) = true := rfl
example : isValue (.succ (.var 0)) = false := rfl

example : eval 0 (.app (.lam .nat (.var 0)) .zero) = .app (.lam .nat (.var 0)) .zero := rfl
example : eval 1 (.app (.app (twice .nat) succFn) .zero) = .app (.lam .nat (.app succFn (.app succFn (.var 0)))) .zero := rfl
example : eval 100 (.app (.app (twice .nat) succFn) .zero) = Term.num 2 := rfl
example : eval 100 (.app (.app (.app (twice (.nat ⇒ .nat)) (twice .nat)) succFn) .zero) = Term.num 4 := rfl
example : eval 100 (.app notFn (.app notFn .tru)) = .tru := rfl
example : eval 100 (.app .tru .zero) = .app .tru .zero := rfl
example : eval 100 (.pred (.succ (.succ .zero))) = .succ .zero := rfl
