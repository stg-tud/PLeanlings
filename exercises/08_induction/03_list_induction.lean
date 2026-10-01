/-
# 08.03 — Induction on lists

Induction works for *every* inductive type, with one case per constructor.
For `List α` there are two constructors, `[]` (`List.nil`) and
`x :: xs` (`List.cons x xs`):

> To prove `P xs` for all lists, prove `P []` and prove that
> `P xs` implies `P (x :: xs)` for every `x`.

    induction xs with
    | nil => …                 -- ⊢ P []
    | cons x xs ih => …        -- ih : P xs   ⊢ P (x :: xs)

Below are our own versions of length, append and map. (We use our own
definitions so that the library's `simp` lemmas don't do all the work.)

Tip: a good first step in each case is `simp [len, app]` (with the
definitions that appear in the goal) and then see what is left. `omega`
can finish goals like `a + 1 + b = a + b + 1`.

## Your task

Prove the three theorems by induction on `xs`.
-/

def len {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => len xs + 1

def app {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys

def mapL {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: mapL f xs

#eval app [1, 2] [3, 4]
#eval mapL (· * 10) [1, 2, 3]

theorem len_app {α : Type} (xs ys : List α) : len (app xs ys) = len xs + len ys := by
  sorry

theorem len_map {α β : Type} (f : α → β) (xs : List α) : len (mapL f xs) = len xs := by
  sorry

theorem map_map {α β γ : Type} (f : β → γ) (g : α → β) (xs : List α) :
    mapL f (mapL g xs) = mapL (fun x => f (g x)) xs := by
  sorry
