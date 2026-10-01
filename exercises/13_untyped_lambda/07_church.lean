/-
# 13.07 — Church encodings

The lambda calculus has no booleans or numbers. But it doesn't need them:
data can be **encoded as functions**. The idea (due to Alonzo Church) is
to represent a piece of data by *what you can do with it*.

## Booleans

A boolean is something that chooses between two alternatives:

    tru = λt. λf. t          (de Bruijn: λ. λ. 1)
    fls = λt. λf. f          (de Bruijn: λ. λ. 0)

Then `if b then x else y` is simply `b x y`. With this, e.g.

    not = λb. b fls tru
    and = λb. λc. b c fls     ("if b then c else false")

## Natural numbers

The numeral `n` is "apply `f` n times":

    0 = λf. λx. x
    1 = λf. λx. f x
    2 = λf. λx. f (f x)
    succ = λn. λf. λx. f (n f x)

Addition: `m + n` applies `f` first `n` times, then `m` more times:
`plus = λm. λn. λf. λx. ?` — that's your job.

## How do we test this?

Call-by-value does not reduce under `λ`, so `plus 1 2` evaluates to some
lambda that *behaves* like `3` but is not literally `3`. To compare, we
use a different strategy: **full β-normalisation** (`norm`, given below),
which reduces everywhere, including under binders, until no β-redex is
left. (It uses the *normal-order* strategy: leftmost-outermost redex
first.) Two terms with the same normal form are equal as programs. Again
we need fuel, since some terms (like Ω) have no normal form.

## Your task

Define `fls`, `not`, `and` and `plus` as `DTerm`s (in de Bruijn notation —
it may help to write the named version first and translate). Any correct
encoding is fine; the checks only compare normal forms.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive DTerm where
  | var (n : Nat)
  | lam (body : DTerm)
  | app (f a : DTerm)
  deriving Repr, DecidableEq, Inhabited

open DTerm

def shift (d c : Nat) : DTerm → DTerm
  | var k => if k < c then var k else var (k + d)
  | lam t => lam (shift d (c + 1) t)
  | app f a => app (shift d c f) (shift d c a)

def unshift (c : Nat) : DTerm → DTerm
  | var k => if k < c then var k else var (k - 1)
  | lam t => lam (unshift (c + 1) t)
  | app f a => app (unshift c f) (unshift c a)

def subst (j : Nat) (s : DTerm) : DTerm → DTerm
  | var k => if k = j then s else var k
  | lam t => lam (subst (j + 1) (shift 1 0 s) t)
  | app f a => app (subst j s f) (subst j s a)

def beta (t v : DTerm) : DTerm := unshift 0 (subst 0 (shift 1 0 v) t)

/-- One step of normal-order reduction (reduces under binders too). -/
def nstep : DTerm → Option DTerm
  | app (lam t) s => some (beta t s)
  | app f a =>
    match nstep f with
    | some f' => some (app f' a)
    | none => (nstep a).map (app f ·)
  | lam t => (nstep t).map lam
  | var _ => none

/-- Normalise with at most `fuel` steps; `none` if fuel runs out. -/
def norm : Nat → DTerm → Option DTerm
  | 0, _ => none
  | n + 1, t =>
    match nstep t with
    | some t' => norm n t'
    | none => some t

/-- `λt. λf. t` -/
def tru : DTerm := lam (lam (var 1))

/-- The Church numeral `n`: `λf. λx. f (f (… (f x)))`. -/
def numeral (n : Nat) : DTerm := lam (lam (go n))
where go : Nat → DTerm
  | 0 => var 0
  | k + 1 => app (var 1) (go k)

/-- `λn. λf. λx. f (n f x)` -/
def succ : DTerm := lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

#eval numeral 2   -- lam (lam (app (var 1) (app (var 1) (var 0))))
#eval norm 100 (app succ (numeral 2)) == some (numeral 3)   -- true

/-! ## Your code -/

/-- `λt. λf. f` -/
def fls : DTerm := sorry

/-- `λb. b fls tru` -/
def not : DTerm := sorry

/-- `λb. λc. b c fls` -/
def and : DTerm := sorry

/-- `λm. λn. λf. λx. m f (n f x)` -/
def plus : DTerm := sorry
