/-
# 01.03 — Currying and partial application

What is the type of a function with two arguments?

    def add (a b : Nat) : Nat := a + b
    #check add          -- add : Nat → Nat → Nat

The arrow associates to the **right**: `Nat → Nat → Nat` means
`Nat → (Nat → Nat)`. So `add` is really a function that takes *one* number
and returns *another function*, which waits for the second number.
This is called **currying** (after Haskell Curry).

Consequently, `add 2 3` is `(add 2) 3`, and you can stop early:

    def addTwo : Nat → Nat := add 2       -- partial application
    #eval addTwo 40                       -- 42

In lambda notation, `add` is `fun a => fun b => a + b`.

## Your task

1. Fill in the **type** of `addTen`, `scale`, and `scaleBy3`.
2. Define `addTen` by partially applying `add`.
3. Define `scaleBy3` by partially applying `scale` (no `fun` needed!).

(Until you fill in the type of `scale`, Lean reports an error at its `fun`,
because it cannot check a function against an unknown type.)
-/

def add (a b : Nat) : Nat := a + b

def addTen : Nat → Nat := add 10

def scale : Nat → Nat → Nat := fun k x => k * x

def scaleBy3 : Nat → Nat := scale 3

#eval addTen 5
#eval scaleBy3 7
