/- HINT
`lookup` recurses through the list. In the case `(y, v) :: rest`, compare
`x == y`; if they differ, look further in `rest`.

In `eval`, the `div` case evaluates both sides with `←`, then checks the
divisor: `if vb == 0 then throw … else pure …`.
-/
def chk_eq : Except String Nat → Except String Nat → Bool
  | .ok a,    .ok b    => a == b
  | .error a, .error b => a == b
  | _,        _        => false
example : Env → String → Except String Nat := lookup
example : Env → Expr → Except String Nat := eval
example : env = [("x", 5), ("y", 0)] := rfl
#guard chk_eq (lookup env "x") (.ok 5)
#guard chk_eq (lookup env "y") (.ok 0)
#guard chk_eq (lookup env "z") (.error "unbound variable: z")
#guard chk_eq (lookup [] "x") (.error "unbound variable: x")
#guard chk_eq (lookup [("a", 1), ("a", 2)] "a") (.ok 1)
#guard chk_eq (lookup [("b", 1), ("a", 2)] "a") (.ok 2)
#guard chk_eq (eval env (.num 3)) (.ok 3)
#guard chk_eq (eval env (.plus (.var "x") (.num 1))) (.ok 6)
#guard chk_eq (eval env (.div (.num 12) (.plus (.var "x") (.num 1)))) (.ok 2)
#guard chk_eq (eval env (.div (.num 1) (.var "y"))) (.error "division by zero")
#guard chk_eq (eval env (.div (.var "y") (.num 0))) (.error "division by zero")
#guard chk_eq (eval env (.var "z")) (.error "unbound variable: z")
#guard chk_eq (eval env (.plus (.var "x") (.var "w"))) (.error "unbound variable: w")
#guard chk_eq (eval env (.plus (.var "q") (.div (.num 1) (.num 0)))) (.error "unbound variable: q")
#guard chk_eq (eval env (.div (.num 1) (.var "u"))) (.error "unbound variable: u")
#guard chk_eq (eval [("n", 9)] (.div (.var "n") (.num 2))) (.ok 4)
