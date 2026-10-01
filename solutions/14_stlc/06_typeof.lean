/-
# 14.06 — A type checker

`HasType` is a relation. To *use* it in a compiler we need an algorithm:

    typeOf : Ctx → Term → Option Ty

which returns `some T` if the term has type `T`, and `none` if it is ill-typed.

Thanks to the type annotations on `λ`, the typing rules are **syntax-directed**:
for each term former exactly one rule applies, and the type of the conclusion
is determined by the types of the subterms. So the checker just follows the rules:

* `var x`: look the variable up in the context.
* `lam A t`: check `t` in `A :: Γ`, and if it has type `B` the result is `A ⇒ B`.
* `app f a`: `f` must have a function type `A ⇒ B` and `a` must have type `A`
  (the *same* `A`: compare with `if A = A' then … else …`; `Ty` has
  decidable equality). The result is `B`.
* `ite c t e`: `c` must be a `bool` and both branches must have the same type.

You can match on several `Option`s at once:

    match typeOf Γ f, typeOf Γ a with
    | some (.arrow A B), some A' => …
    | _, _ => none

(In the next chapter we prove that `typeOf` is correct: it returns `some T`
exactly when `HasType Γ t T` holds.)

## Your task

Fill in the cases for variables, applications and conditionals.
-/

/-! ## Given (from earlier exercises) — do not edit -/

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

/-- A context lists the types of the free variables: `Γ[0]?` is the type of `var 0`. -/
abbrev Ctx := List Ty

/-! ## The type checker -/

def typeOf (Γ : Ctx) : Term → Option Ty
  | .var x => Γ[x]?
  | .lam A t =>
    match typeOf (A :: Γ) t with
    | some B => some (A ⇒ B)
    | none => none
  | .app f a =>
    match typeOf Γ f, typeOf Γ a with
    | some (.arrow A B), some A' => if A = A' then some B else none
    | _, _ => none
  | .tru => some .bool
  | .fls => some .bool
  | .ite c t e =>
    match typeOf Γ c, typeOf Γ t, typeOf Γ e with
    | some .bool, some A, some A' => if A = A' then some A else none
    | _, _, _ => none
  | .zero => some .nat
  | .succ t =>
    match typeOf Γ t with
    | some .nat => some .nat
    | _ => none
  | .pred t =>
    match typeOf Γ t with
    | some .nat => some .nat
    | _ => none
  | .iszero t =>
    match typeOf Γ t with
    | some .nat => some .bool
    | _ => none

#eval typeOf [] (.lam (.nat ⇒ .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0)))))
#eval typeOf [] (.app .tru .zero)
