/- HINT
The `leaf` case is the base case. In the `node l v r` case, call the
function on both `l` and `r` and combine the results.

For `mirror`, the new node has the mirrored *right* subtree on the left.
-/
example : Tree → Nat := Tree.size
example : Tree → Nat := Tree.sum
example : Tree → Tree := Tree.mirror
example : example1 =
    .node (.node .leaf 2 .leaf) 4 (.node .leaf 7 (.node .leaf 9 .leaf)) := rfl
example : Tree.leaf.size = 0 := rfl
example : example1.size = 4 := rfl
example : (Tree.node .leaf 5 .leaf).size = 1 := rfl
example : Tree.leaf.sum = 0 := rfl
example : example1.sum = 22 := rfl
example : (Tree.node (.node .leaf 1 .leaf) 0 .leaf).sum = 1 := rfl
example : Tree.leaf.mirror = .leaf := rfl
example : example1.mirror =
    .node (.node (.node .leaf 9 .leaf) 7 .leaf) 4 (.node .leaf 2 .leaf) := rfl
example : example1.mirror.mirror = example1 := rfl
example : (Tree.node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)).mirror =
    .node (.node .leaf 3 .leaf) 2 (.node .leaf 1 .leaf) := rfl
