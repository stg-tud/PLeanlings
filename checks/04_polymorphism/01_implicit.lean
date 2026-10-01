/- HINT
`swap` looks exactly like the `Nat`-only version from chapter 02, only
the types are more general.

For `applyTwice`: `f` is applied to `x` and to `f x`, so `f` must take an
`α` and return an `α`.
-/
example : {α β : Type} → α × β → β × α := @swap
example : {α β : Type} → α → β → α := @const
example : {α : Type} → (α → α) → α → α := @applyTwice
#guard swap (1, "one") = ("one", 1)
#guard swap (true, 'c') = ('c', true)
#guard const 1 "ignored" = 1
#guard const "x" 5 = "x"
#guard applyTwice (· ++ "!") "hey" = "hey!!"
#guard applyTwice (· * 3) 2 = 18
#guard applyTwice (fun (p : Nat × Nat) => (p.2, p.1 + p.2)) (0, 1) = (1, 2)
