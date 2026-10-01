/-
# 14.01 — The simply typed lambda calculus: types and terms

In chapter 13 you met the *untyped* lambda calculus. It is tiny and
Turing-complete, but it also accepts nonsense such as `true 0` (applying a
boolean as if it were a function) and programs that never finish, such as `Ω`.
The **simply typed lambda calculus** (STLC) rules these out. Every function
parameter gets a type annotation, and a type checker rejects bad programs
*before* they run.

Over the next three chapters you will define STLC, write a type checker and an
interpreter for it, and prove its central theorem: **well-typed programs do
not go wrong**.

Our STLC has the booleans and numbers of chapters 11–12 as base types, plus
function types:

    T ::= bool | nat | T ⇒ T

    t ::= x | λx:T. t | t t
        | true | false | if t then t else t
        | 0 | succ t | pred t | iszero t

The function type is `Ty.arrow A B`, and we write it `A ⇒ B`. The arrow
associates to the **right**: `.nat ⇒ .nat ⇒ .bool` means
`.nat ⇒ (.nat ⇒ .bool)`, which is the (curried) type of a function taking two
numbers. If the argument itself is a function you need parentheses:
`(.nat ⇒ .nat) ⇒ .nat`.

## Variables are de Bruijn indices

As in chapter 13 we use **de Bruijn indices**. A variable is a number: how
many `λ`s you have to cross, going outwards, to reach its binder. `.var 0`
is bound by the nearest enclosing `λ`, `.var 1` by the next one out, and so
on. The binder `.lam A body` has no name, only the type `A` of its parameter.

| named                     | de Bruijn                                    |
|---------------------------|----------------------------------------------|
| `λx:nat. x`               | `.lam .nat (.var 0)`                         |
| `λx:nat. λy:bool. y`      | `.lam .nat (.lam .bool (.var 0))`            |
| `λx:nat. λy:bool. x`      | `.lam .nat (.lam .bool (.var 1))`            |
| `λf:nat⇒nat. f 0`         | `.lam (.nat ⇒ .nat) (.app (.var 0) .zero)`   |

The pay-off: α-equivalent terms such as `λx. x` and `λy. y` are literally
*equal*, and we will never have to rename bound variables to avoid capture.

A variable that points beyond all enclosing binders (for example `.var 0` on its
own) is **free**. Its type comes from a *context*, which is the topic of the
next exercise.

## Your task

Write the following as Lean values:

1. `idBool` : `λx:bool. x`
2. `constNat` : `λx:nat. λy:bool. x` (ignores its second argument)
3. `applyFn` : `λf:nat⇒bool. λx:nat. f x`
4. `notFn` : `λb:bool. if b then false else true`
5. `twiceTy` : the type `(nat ⇒ nat) ⇒ nat ⇒ nat`
6. `twice` : `λf:nat⇒nat. λx:nat. f (f x)`
-/

/-- Types: `T ::= bool | nat | T ⇒ T`. -/
inductive Ty where
  | bool
  | nat
  | arrow (A B : Ty)
  deriving DecidableEq, Repr

/-- `A ⇒ B` is the function type. It associates to the right. -/
infixr:70 " ⇒ " => Ty.arrow

/-- Terms with de Bruijn indices. `lam A t` binds variable `0` (of type `A`) in `t`. -/
inductive Term where
  | var (x : Nat)
  | lam (A : Ty) (body : Term)
  | app (f a : Term)
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving DecidableEq, Repr

-- Two examples:
def idNat : Term := .lam .nat (.var 0)
def boolToNat : Ty := .bool ⇒ .nat

def idBool : Term := .lam .bool (.var 0)

def constNat : Term := .lam .nat (.lam .bool (.var 1))

def applyFn : Term := .lam (.nat ⇒ .bool) (.lam .nat (.app (.var 1) (.var 0)))

def notFn : Term := .lam .bool (.ite (.var 0) .fls .tru)

def twiceTy : Ty := (.nat ⇒ .nat) ⇒ .nat ⇒ .nat

def twice : Term := .lam (.nat ⇒ .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0))))
