/- HINT
Follow the equations in the explanation literally. `exts σ 0` is `.var 0`,
`exts σ (n + 1)` shifts `σ n` with `rename Nat.succ`. `subst σ (.var x)` is just
`σ x`. Under a `lam` continue with `exts σ`.
-/

example : exts (fun n => .var (n + 7)) 0 = .var 0 := rfl
example : exts (fun n => .var (n + 7)) 2 = .var 9 := rfl
example : exts (fun _ => .lam .nat (.var 1)) 1 = .lam .nat (.var 2) := rfl
example : subst (subst1 .tru) (.var 0) = .tru := rfl
example : subst (subst1 .tru) (.var 3) = .var 2 := rfl
example : subst (subst1 .tru) (.lam .nat (.app (.var 1) (.var 0))) = .lam .nat (.app .tru (.var 0)) := rfl
example : subst (subst1 (.var 0)) (.lam .nat (.var 1)) = .lam .nat (.var 1) := rfl
example : subst (subst1 (.var 0)) (.lam .nat (.lam .nat (.app (.var 2) (.var 3)))) = .lam .nat (.lam .nat (.app (.var 2) (.var 2))) := rfl
example : subst (fun n => .succ (.var n)) (.ite (.var 0) .zero (.pred (.var 2))) = .ite (.succ (.var 0)) .zero (.pred (.succ (.var 2))) := rfl
example : subst (subst1 .zero) (.ite (.var 0) (.succ (.var 1)) (.iszero (.pred .fls))) = .ite .zero (.succ (.var 0)) (.iszero (.pred .fls)) := rfl
