/- HINT
For each variable, count the `λ`s between the variable and its binder. The
innermost binder is `0`. In `λf. λx. f x` the `f` sits under two binders
(`λx` is in between), so it is `.var 1`.

`if b then false else true` is `.ite (.var 0) .fls .tru`. Application is `.app f a`.
-/

example : idBool = .lam .bool (.var 0) := rfl
example : constNat = .lam .nat (.lam .bool (.var 1)) := rfl
example : applyFn = .lam (.arrow .nat .bool) (.lam .nat (.app (.var 1) (.var 0))) := rfl
example : notFn = .lam .bool (.ite (.var 0) .fls .tru) := rfl
example : twiceTy = .arrow (.arrow .nat .nat) (.arrow .nat .nat) := rfl
example : twice = .lam (.arrow .nat .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0)))) := rfl
