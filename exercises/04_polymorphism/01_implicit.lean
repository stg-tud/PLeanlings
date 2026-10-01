/-
# 04.01 — Polymorphism and implicit arguments

So far, all our functions worked on one specific type. But the identity
function, or `swap` on pairs, does not care what the types are. In Lean, the
*type itself* can be an argument:

    def identity (α : Type) (x : α) : α := x
    #eval identity Nat 5            -- 5
    #eval identity String "hi"      -- "hi"

This is **parametric polymorphism** (like generics `<T>` in Java). Always
passing the type is tedious, and Lean can figure it out from `x` anyway. So
we make the argument **implicit** with curly braces:

    def id' {α : Type} (x : α) : α := x
    #eval id' 5                     -- Lean infers α := Nat

Implicit arguments are filled in by Lean automatically. If you ever need to
give one explicitly, write `id' (α := Nat) 5`, or `@id' Nat 5` (the `@`
makes *all* arguments explicit).

The type of `id'` is `{α : Type} → α → α`. Note that the result type
mentions the argument `α`: this is a **dependent** function type, which is
what makes Lean so expressive.

## Your task

1. Implement `swap`, which swaps the components of a pair, for any types.
2. Implement `const x y`, which ignores `y` and returns `x`.
3. `applyTwice` is the polymorphic version of `twice` from chapter 01.
   Fill in the types of its arguments and its result. (Until you do, Lean
   complains that `f` is not a function: it does not know its type yet.)
-/

def id' {α : Type} (x : α) : α := x

#eval id' 5
#check @id'

def swap {α β : Type} (p : α × β) : β × α := sorry

def const {α β : Type} (x : α) (_y : β) : α := sorry

def applyTwice {α : Type} (f : sorry) (x : sorry) : sorry := f (f x)
