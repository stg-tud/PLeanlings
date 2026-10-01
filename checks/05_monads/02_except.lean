/- HINT
`if … then throw "…" else pure …` covers `safeDiv` and `digit`.
`Char.isDigit` tells you whether a character is a digit.

For `twoDigits`, match on `s.toList` with a case `[c1, c2]` and a
catch-all case. In the first case, open a `do` block and use `←` twice.
`orDefault` is a plain `match` on `.ok n` and `.error _`.
-/
def chk_eq : Except String Nat → Except String Nat → Bool
  | .ok a,    .ok b    => a == b
  | .error a, .error b => a == b
  | _,        _        => false
example : Nat → Nat → Except String Nat := safeDiv
example : Char → Except String Nat := digit
example : String → Except String Nat := twoDigits
example : Except String Nat → Nat → Nat := orDefault
#guard chk_eq (safeDiv 7 2) (.ok 3)
#guard chk_eq (safeDiv 7 0) (.error "division by zero")
#guard chk_eq (safeDiv 0 0) (.error "division by zero")
#guard chk_eq (digit '0') (.ok 0)
#guard chk_eq (digit '7') (.ok 7)
#guard chk_eq (digit '9') (.ok 9)
#guard chk_eq (digit 'a') (.error "not a digit: a")
#guard chk_eq (digit ' ') (.error "not a digit:  ")
#guard chk_eq (twoDigits "42") (.ok 42)
#guard chk_eq (twoDigits "07") (.ok 7)
#guard chk_eq (twoDigits "99") (.ok 99)
#guard chk_eq (twoDigits "4x") (.error "not a digit: x")
#guard chk_eq (twoDigits "?x") (.error "not a digit: ?")
#guard chk_eq (twoDigits "123") (.error "expected two digits")
#guard chk_eq (twoDigits "") (.error "expected two digits")
#guard chk_eq (twoDigits "5") (.error "expected two digits")
#guard orDefault (.ok 5) 0 = 5
#guard orDefault (.error "boom") 3 = 3
#guard orDefault (twoDigits "12") 0 = 12
