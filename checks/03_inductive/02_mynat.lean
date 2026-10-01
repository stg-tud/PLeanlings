/- HINT
Look at `double` for the shape. For `add`, the `zero` case returns `m`, and
the `succ n` case puts a `.succ` around a recursive call `add m n`.

For `mul`: `m * (n + 1) = m * n + m`, so the `succ n` case is
`add (mul m n) m`.
-/
example : MyNat → MyNat → MyNat := MyNat.add
example : MyNat → MyNat → MyNat := MyNat.mul
def check_add (a b : Nat) : Bool := ((MyNat.ofNat a).add (MyNat.ofNat b)).toNat == a + b
def check_mul (a b : Nat) : Bool := ((MyNat.ofNat a).mul (MyNat.ofNat b)).toNat == a * b
example : check_add 0 0 = true := rfl
example : check_add 3 0 = true := rfl
example : check_add 0 5 = true := rfl
example : check_add 3 4 = true := rfl
example : check_add 10 7 = true := rfl
example : check_mul 0 0 = true := rfl
example : check_mul 5 0 = true := rfl
example : check_mul 0 5 = true := rfl
example : check_mul 1 6 = true := rfl
example : check_mul 3 4 = true := rfl
example : check_mul 7 6 = true := rfl
