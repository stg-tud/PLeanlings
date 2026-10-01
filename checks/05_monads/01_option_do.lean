/- HINT
Each step that might fail gets its own line `let v ← …`. At the end,
`pure (…)` returns the combined result.

In `divChain`, the last step may itself fail, so it can simply be
`safeDiv q c` (without `pure`).
-/
example : List Nat → List Nat → Option Nat := addHeads
example : List Nat → Option Nat := sumFirstTwo
example : Nat → Nat → Nat → Option Nat := divChain
#guard addHeads [1, 2] [10] = some 11
#guard addHeads [] [10] = none
#guard addHeads [1] [] = none
#guard addHeads [0] [0, 5] = some 0
#guard sumFirstTwo [5] = none
#guard sumFirstTwo [] = none
#guard sumFirstTwo [5, 6] = some 11
#guard sumFirstTwo [1, 2, 100] = some 3
#guard divChain 100 5 2 = some 10
#guard divChain 100 0 2 = none
#guard divChain 100 5 0 = none
#guard divChain 7 2 2 = some 1
