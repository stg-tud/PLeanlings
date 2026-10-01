/- HINT
Use `if … then none else some …` for `safeDiv`, and pattern matching on the
list for `head?`.

For `addOpt`, match on both arguments: only the case `some x, some y`
gives a result; `| _, _ => none` catches everything else.
-/
example : Nat → Nat → Option Nat := safeDiv
example : List Nat → Option Nat := head?
example : Option Nat → Option Nat → Option Nat := addOpt
example : safeDiv 10 2 = some 5 := rfl
example : safeDiv 7 2 = some 3 := rfl
example : safeDiv 10 0 = none := rfl
example : safeDiv 0 0 = none := rfl
example : safeDiv 0 3 = some 0 := rfl
example : head? [3, 1, 4] = some 3 := rfl
example : head? [] = none := rfl
example : head? [0] = some 0 := rfl
example : addOpt (some 1) (some 2) = some 3 := rfl
example : addOpt (some 1) none = none := rfl
example : addOpt none (some 1) = none := rfl
example : addOpt none none = none := rfl
