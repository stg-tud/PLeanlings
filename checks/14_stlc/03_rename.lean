/- HINT
`ext ρ` must send `0` to `0` and `n + 1` to `ρ n + 1`. In `rename`, a variable
`x` is simply mapped to `ρ x`. For an application rename both sides, and for
`lam A t` keep `A` and rename the body with `ext ρ`.
-/

example : ext Nat.succ 0 = 0 := rfl
example : ext Nat.succ 3 = 4 := rfl
example : ext (· + 10) 2 = 12 := rfl
example : ext (ext (· + 10)) 1 = 1 := rfl
example : rename Nat.succ (.var 0) = .var 1 := rfl
example : rename (· * 2) (.var 3) = .var 6 := rfl
example : rename Nat.succ (.lam .nat (.app (.var 0) (.var 1))) = .lam .nat (.app (.var 0) (.var 2)) := rfl
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 1))) (.var 0)) = .app (.lam .bool (.lam .bool (.var 1))) (.var 5) := rfl
example : rename Nat.succ (.ite (.var 0) (.succ (.var 1)) (.iszero (.pred .zero))) = .ite (.var 1) (.succ (.var 2)) (.iszero (.pred .zero)) := rfl
