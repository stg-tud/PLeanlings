/- HINT
Each function has one case for `.nil` and one for `.cons x xs`. In the
`.cons` case, call the function recursively on `xs`.

To reverse `cons x xs`: reverse `xs`, then append the one-element list
`.cons x .nil` at the end.
-/
example : NatList → Nat := NatList.length
example : NatList → NatList → NatList := NatList.append
example : NatList → NatList := NatList.reverse
example : (NatList.ofList []).length = 0 := rfl
example : (NatList.ofList [5]).length = 1 := rfl
example : (NatList.ofList [1, 2, 3, 4]).length = 4 := rfl
example : ((NatList.ofList [1, 2]).append (NatList.ofList [3, 4])).toList = [1, 2, 3, 4] := rfl
example : ((NatList.ofList []).append (NatList.ofList [3, 4])).toList = [3, 4] := rfl
example : ((NatList.ofList [1, 2]).append (NatList.ofList [])).toList = [1, 2] := rfl
example : (NatList.ofList [1, 2, 3]).reverse.toList = [3, 2, 1] := rfl
example : (NatList.ofList []).reverse.toList = [] := rfl
example : (NatList.ofList [7]).reverse.toList = [7] := rfl
example : (NatList.ofList [1, 2, 3, 4, 5]).reverse.toList = [5, 4, 3, 2, 1] := rfl
