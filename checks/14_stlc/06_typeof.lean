/- HINT
The variable case is a single list lookup `Γ[x]?`. For an application, match on
`typeOf Γ f, typeOf Γ a` and accept only `some (.arrow A B), some A'` with
`A = A'`. The conditional is similar with three results, where the first
must be `some .bool`.
-/

example : typeOf [.bool, .nat] (.var 1) = some .nat := rfl
example : typeOf [.bool] (.var 1) = none := rfl
example : typeOf [] (.lam .nat (.var 0)) = some (.nat ⇒ .nat) := rfl
example : typeOf [.nat ⇒ .bool] (.app (.var 0) .zero) = some .bool := rfl
example : typeOf [.nat ⇒ .bool] (.app (.var 0) .tru) = none := rfl
example : typeOf [] (.app .tru .zero) = none := rfl
example : typeOf [] (.app .zero .zero) = none := rfl
example : typeOf [] (.lam (.nat ⇒ .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0))))) = some ((.nat ⇒ .nat) ⇒ .nat ⇒ .nat) := rfl
example : typeOf [] (.ite .tru .zero (.succ .zero)) = some .nat := rfl
example : typeOf [] (.ite (.iszero .zero) .fls .tru) = some .bool := rfl
example : typeOf [] (.ite .tru .zero .fls) = none := rfl
example : typeOf [] (.ite .zero .zero .zero) = none := rfl
example : typeOf [] (.ite (.var 0) .zero .zero) = none := rfl
example : typeOf [] (.lam .bool (.ite (.var 0) (.lam .nat (.var 0)) (.lam .nat (.succ (.var 0))))) = some (.bool ⇒ .nat ⇒ .nat) := rfl
