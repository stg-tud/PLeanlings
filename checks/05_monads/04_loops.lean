/- HINT
Start with `let mut m := 0`, then `for x in xs do` and update `m` inside
an `if`. Finish with `return m`.

For `freshNames`, start with `let mut names := []`, and loop `k` times with
`for _ in [0:k] do`. In the loop body, `let n ← fresh` gets a number, and
`names := names ++ [s!"x{n}"]` appends a name.
-/
example : StateM Nat Nat := fresh
example : List Nat → Nat := maxList
example : (Nat → Bool) → List Nat → Nat := countIf
example : Nat → StateM Nat (List String) := freshNames
#guard Id.run (fresh.run 4) = (4, 5)
#guard maxList [3, 9, 2] = 9
#guard maxList [] = 0
#guard maxList [1] = 1
#guard maxList [5, 4, 3] = 5
#guard maxList [1, 2, 3] = 3
#guard countIf (· > 2) [1, 2, 3, 4] = 2
#guard countIf (· > 2) [] = 0
#guard countIf (fun _ => true) [7, 7, 7] = 3
#guard countIf (· % 2 == 0) [1, 3, 5] = 0
#guard Id.run ((freshNames 3).run 0) = (["x0", "x1", "x2"], 3)
#guard Id.run ((freshNames 0).run 7) = ([], 7)
#guard Id.run ((freshNames 2).run 10) = (["x10", "x11"], 12)
