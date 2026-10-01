/- HINT
The *total* number of elements in both lists gets smaller by one in each
call, even though the lists swap places.

Write `termination_by xs.length + ys.length` on a new line directly after
the `match` cases (not indented further than `def`'s body).
-/
example : List Nat → List Nat → List Nat := interleave
example : Nat → Nat := digitSum
#guard interleave [1, 2, 3] [10, 20] = [1, 10, 2, 20, 3]
#guard interleave [] [1, 2] = [1, 2]
#guard interleave [1, 2] [] = [1, 2]
#guard interleave [1] [10, 20, 30] = [1, 10, 20, 30]
#guard digitSum 0 = 0
#guard digitSum 7 = 7
#guard digitSum 10 = 1
#guard digitSum 1234 = 10
#guard digitSum 99999 = 45
