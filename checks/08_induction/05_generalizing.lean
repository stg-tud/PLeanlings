/- HINT
Use `induction xs generalizing acc with …`, so that `ih` works for every
accumulator. Then `simp [revAcc, rev, app, ih, app_assoc]`.

`fastRev_eq` needs no induction: unfold `fastRev` and use `revAcc_eq` and
`app_nil`. In `sumAcc_eq`, finish the `cons` case with `omega`.
-/
example : fastRev [1, 2, 3] = [3, 2, 1] := rfl
example : sumAcc [1, 2, 3] 10 = 16 := rfl
example : sum [1, 2, 3] = 6 := rfl
example {α : Type} (x : α) (xs acc : List α) : revAcc (x :: xs) acc = revAcc xs (x :: acc) := rfl
example (x : Nat) (xs : List Nat) (acc : Nat) : sumAcc (x :: xs) acc = sumAcc xs (acc + x) := rfl
example {α : Type} (x : α) (xs : List α) : rev (x :: xs) = app (rev xs) [x] := rfl
example {α : Type} (xs acc : List α) : revAcc xs acc = app (rev xs) acc := revAcc_eq xs acc
example {α : Type} (xs : List α) : fastRev xs = rev xs := fastRev_eq xs
example (xs : List Nat) (acc : Nat) : sumAcc xs acc = sum xs + acc := sumAcc_eq xs acc
