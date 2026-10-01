/- HINT
Every lemma is an induction on `xs`. Pass the definitions and the earlier
lemmas to `simp`, e.g. `simp [app, rev, ih, app_assoc]`.

In `rev_app`, the `nil` case needs `app_nil` and the `cons` case needs
`app_assoc`. In `rev_rev`, the `cons` case needs `rev_app`.
-/
example : rev [1, 2, 3] = [3, 2, 1] := rfl
example : app [1, 2] [3] = [1, 2, 3] := rfl
example {α : Type} (x : α) (xs : List α) : rev (x :: xs) = app (rev xs) [x] := rfl
example {α : Type} (x : α) (xs ys : List α) : app (x :: xs) ys = x :: app xs ys := rfl
example {α : Type} (xs : List α) : app xs [] = xs := app_nil xs
example {α : Type} (xs ys zs : List α) : app (app xs ys) zs = app xs (app ys zs) := app_assoc xs ys zs
example {α : Type} (xs ys : List α) : rev (app xs ys) = app (rev ys) (rev xs) := rev_app xs ys
example {α : Type} (xs : List α) : rev (rev xs) = xs := rev_rev xs
