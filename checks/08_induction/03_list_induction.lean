/- HINT
Use `induction xs with | nil => … | cons x xs ih => …`. In each case,
`simp` with the relevant definitions and `ih`.

For `len_app`, after `simp [app, len, ih]` an arithmetic goal may remain:
finish it with `omega`.
-/
example : len [1, 2, 3] = 3 := rfl
example : app [1, 2] [3] = [1, 2, 3] := rfl
example : mapL (· + 1) [1, 2] = [2, 3] := rfl
example {α : Type} (x : α) (xs ys : List α) : app (x :: xs) ys = x :: app xs ys := rfl
example {α : Type} (x : α) (xs : List α) : len (x :: xs) = len xs + 1 := rfl
example {α : Type} (xs ys : List α) : len (app xs ys) = len xs + len ys := len_app xs ys
example {α β : Type} (f : α → β) (xs : List α) : len (mapL f xs) = len xs := len_map f xs
example {α β γ : Type} (f : β → γ) (g : α → β) (xs : List α) :
    mapL f (mapL g xs) = mapL (fun x => f (g x)) xs := map_map f g xs
