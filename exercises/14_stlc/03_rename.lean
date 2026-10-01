/-
# 14.03 — Renaming

To run a program we must substitute arguments for parameters, and substitution
needs to *shift* variables (chapter 13). This time we use a cleaner and more
general toolkit that is popular in mechanised metatheory (PLFA, Autosubst):

* a **renaming** `ρ : Nat → Nat` says where every free variable goes
  (this exercise),
* a **substitution** `σ : Nat → Term` says which term replaces every free
  variable (next exercise).

`rename ρ t` applies `ρ` to every *free* variable of `t`. The only subtle case
is going under a binder. Inside `lam A body`, index `0` is the bound variable
and must stay `0`. Index `n + 1` inside the body is the outer variable `n`, which
goes to `ρ n`. Seen from inside the body that is `ρ n + 1`, because one more
binder now lies in between. This is captured by

    ext ρ 0       = 0
    ext ρ (n + 1) = ρ n + 1

and `rename ρ (lam A body) = lam A (rename (ext ρ) body)`.

The shift of chapter 13 ("add one to every free variable") is now simply
`rename Nat.succ`. For example

    rename Nat.succ (.lam .nat (.app (.var 0) (.var 1)))
      = .lam .nat (.app (.var 0) (.var 2))

since the bound `var 0` stays put and the free variable (`var 1` inside the
λ, i.e. free variable `0`) is shifted.

Why the generality? In the next chapter a *single* lemma about `rename ρ`
gives us weakening, exchange, and every other structural property we need.

## Your task

1. Define `ext`.
2. Fill in the missing cases of `rename` (variables, abstractions, applications).
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

def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => sorry
  | n + 1 => sorry

def rename (ρ : Nat → Nat) : Term → Term
  | .var x => sorry
  | .lam A t => sorry
  | .app f a => sorry
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .pred t => .pred (rename ρ t)
  | .iszero t => .iszero (rename ρ t)
