/-
# 13.03 — De Bruijn indices

Names are for humans. A machine only needs to know *which binder* a
variable refers to. **De Bruijn indices** replace each variable by a
number: how many `λ`s you have to cross (going outwards) to reach its
binder. Binders themselves carry no name at all.

    λx. x                 ↦   λ. 0
    λx. λy. x             ↦   λ. λ. 1
    λx. λy. y             ↦   λ. λ. 0
    λx. x (λy. x y)       ↦   λ. 0 (λ. 1 0)

Note how the *same* variable `x` is `0` in one place and `1` in another:
the index depends on how deep we are.

The big win: **α-equivalent terms become literally equal.** `λx. x` and
`λy. y` are both `λ. 0`, so Lean's `=` *is* α-equivalence. No more fresh
names. (The price: indices are hard to read and must be adjusted when a
term moves under a binder — next exercise.)

    inductive DTerm where
      | var (n : Nat)
      | lam (body : DTerm)
      | app (f a : DTerm)

**Translation.** To convert a named term, keep a *context*: the list of
names bound by the enclosing `λ`s, innermost first. A variable's index is
its position in that list (the first match, which handles shadowing:
in `λx. λx. x` the inner `x` wins). Entering `λx. t` pushes `x` on the
front. A variable not in the context is free and has no index; we return
`none` then.

    toDB Γ x        = position of x in Γ
    toDB Γ (λx. t)  = λ. toDB (x :: Γ) t
    toDB Γ (t₁ t₂)  = toDB Γ t₁  toDB Γ t₂

## Your task

1. Write `K_db` (`λx y. x`), `S_db` (`λx y z. x z (y z)`) and `omega_db`
   (`λx. x x`) by hand.
2. Implement `toDB`. The helper `indexOf` is given.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Term where
  | var (x : String)
  | lam (x : String) (body : Term)
  | app (f a : Term)
  deriving Repr, DecidableEq, Inhabited

inductive DTerm where
  | var (n : Nat)
  | lam (body : DTerm)
  | app (f a : DTerm)
  deriving Repr, DecidableEq, Inhabited

/-- Position of the first occurrence of `x` in the list, if any. -/
def indexOf (x : String) : List String → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf x ys).map (· + 1)

/-! ## Your code -/

/-- `λx. λy. x` -/
def K_db : DTerm := sorry

/-- `λx. λy. λz. x z (y z)` -/
def S_db : DTerm := sorry

/-- `λx. x x` -/
def omega_db : DTerm := sorry

/-- Translate a named term to de Bruijn form, in context `Γ` (innermost first). -/
def toDB (Γ : List String) : Term → Option DTerm
  | .var x => sorry
  | .lam x b => sorry
  | .app f a => sorry
