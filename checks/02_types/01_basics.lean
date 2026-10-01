/- HINT
Evaluate the expressions on a scratch line, e.g. `#eval (3 : Nat) - 5`.
Remember that `Nat` has no negative numbers.

Strings are joined with `++`. Characters are compared with `==` and
written in single quotes, like `' '`. Combine booleans with `||`.
-/
example : natDiff = 0 := rfl
example : intDiff = -2 := rfl
example : natQuot = 3 := rfl
example : String → String := shout
example : Char → Bool := isDigitOrSpace
#guard shout "hello" = "hello!"
#guard shout "" = "!"
#guard shout "a!" = "a!!"
#guard isDigitOrSpace '7' = true
#guard isDigitOrSpace '0' = true
#guard isDigitOrSpace ' ' = true
#guard isDigitOrSpace 'a' = false
#guard isDigitOrSpace '_' = false
