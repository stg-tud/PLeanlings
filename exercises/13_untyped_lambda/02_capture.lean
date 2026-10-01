/-
# 13.02 — Substitution and variable capture

Computation in the lambda calculus is a single rule, **β-reduction**:

    (λx. t) s  ⟶  [x := s] t

"call the function by replacing its parameter with the argument". So
everything hinges on **substitution** `[x := s] t`: replace the *free*
occurrences of `x` in `t` by `s`. A first attempt:

    [x := s] x        = s
    [x := s] y        = y                        (y ≠ x)
    [x := s] (λx. t)  = λx. t                    (x is shadowed: stop)
    [x := s] (λy. t)  = λy. [x := s] t           (y ≠ x)
    [x := s] (t₁ t₂)  = ([x := s] t₁) ([x := s] t₂)

This looks right, but it has a famous bug: **variable capture**. Take

    [x := y] (λy. x)

The function `λy. x` ignores its argument and returns the *outer* `x`.
After substituting the free variable `y` for `x` we should get a function
that returns that outer `y`. Naive substitution produces `λy. y` — the
identity! The free `y` we inserted was *captured* by the binder `λy`.

The fix is to rename bound variables first: `λy. x` and `λz. x` mean the
same function. Terms that differ only in the names of bound variables are
called **α-equivalent**, and on paper one silently works "up to α". So we
would compute `[x := y] (λz. x) = λz. y`. Correct!

In a proof assistant this is painful:
* we must invent fresh names,
* substitution is no longer structurally recursive (we rename, then recurse),
* `=` on `Term` is not α-equivalence, so `λx. x ≠ λy. y` in Lean, and
  every lemma must be stated "up to α".

The next exercise shows a representation that makes all of this go away.

## Your task

1. Implement the naive `subst x s t` exactly as in the equations above.
2. Implement `substChecked x s t`, which behaves like `subst` but returns
   `none` when substitution would go under a binder `λy` with `y` free in
   `s` *and* actually has to substitute something there (i.e. `x` is free
   in that lambda's body). Otherwise it returns `some` of the result.
   `fv` (given) and `List.contains` will help.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Term where
  | var (x : String)
  | lam (x : String) (body : Term)
  | app (f a : Term)
  deriving Repr, DecidableEq, Inhabited

open Term

def fv : Term → List String
  | var x => [x]
  | lam x b => (fv b).filter (· != x)
  | app f a => fv f ++ fv a

/-! ## Your code -/

/-- Naive (capturing!) substitution `[x := s] t`. -/
def subst (x : String) (s : Term) : Term → Term
  | var y => sorry
  | lam y b => sorry
  | app f a => sorry

/-- Substitution that refuses (with `none`) to capture variables. -/
def substChecked (x : String) (s : Term) : Term → Option Term
  | var y => sorry
  | lam y b => sorry
  | app f a => sorry

-- Once you are done, try these. The first one shows the capture bug:
-- #eval subst "x" (var "y") (lam "y" (var "x"))          -- lam "y" (var "y")  (wrong!)
-- #eval substChecked "x" (var "y") (lam "y" (var "x"))   -- none
-- #eval substChecked "x" (var "y") (lam "z" (var "x"))   -- some (lam "z" (var "y"))
