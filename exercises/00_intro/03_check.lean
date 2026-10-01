/-
# 00.03 — Everything has a type

In Lean **every** expression has a type, and `#check` shows it:

    #check 5            -- 5 : Nat
    #check true         -- Bool.true : Bool
    #check "hi"         -- "hi" : String
    #check Nat.succ     -- Nat.succ (n : Nat) : Nat

Even types have types. `Nat : Type` says that `Nat` is a type. This
"types all the way down" idea will matter a lot later in the course.

The arrow `→` describes functions. `Nat → Bool` is the type of functions that
take a natural number and return a boolean.

## Your task

Fill in the *types* of the following definitions (replace each `sorry` after
the colon). Use `#check` on the right-hand sides to find out.
-/

def a : sorry := Nat.mul 7 6
def b : sorry := true && !false
def c : sorry := "three" ++ "four"
def d : sorry := Nat.succ
def e : sorry := Nat
