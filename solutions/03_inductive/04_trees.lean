/-
# 03.04 — Binary trees

A binary tree of numbers is either an empty `leaf`, or a `node` with a left
subtree, a value, and a right subtree:

    inductive Tree where
      | leaf : Tree
      | node (left : Tree) (value : Nat) (right : Tree) : Tree

           4                node (node leaf 2 leaf) 4
          / \                    (node leaf 7 (node leaf 9 leaf))
         2   7
              \
               9

Now there are *two* recursive arguments, so a recursive function typically
calls itself on both subtrees:

    def Tree.height : Tree → Nat
      | .leaf       => 0
      | .node l _ r => max l.height r.height + 1

Trees are everywhere in programming languages: a program's abstract syntax
is a tree, as you will see in the next exercise.

## Your task

1. `Tree.size t`: the number of `node`s in `t`.
2. `Tree.sum t`: the sum of all values in `t`.
3. `Tree.mirror t`: the mirror image (swap left and right, everywhere).
-/

inductive Tree where
  | leaf : Tree
  | node (left : Tree) (value : Nat) (right : Tree) : Tree
deriving Repr

def Tree.height : Tree → Nat
  | .leaf       => 0
  | .node l _ r => max l.height r.height + 1

def Tree.size : Tree → Nat
  | .leaf       => 0
  | .node l _ r => l.size + 1 + r.size

def Tree.sum : Tree → Nat
  | .leaf       => 0
  | .node l v r => l.sum + v + r.sum

def Tree.mirror : Tree → Tree
  | .leaf       => .leaf
  | .node l v r => .node r.mirror v l.mirror

def example1 : Tree :=
  .node (.node .leaf 2 .leaf) 4 (.node .leaf 7 (.node .leaf 9 .leaf))

#eval example1.size
#eval example1.sum
#eval example1.mirror
