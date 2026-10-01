/-
# 13.05 — Call-by-value small-step semantics

Like for the arithmetic language in chapter 11, we define evaluation as a
**small-step relation** `Step t t'` ("`t` reduces to `t'` in one step").

The only **values** are lambdas: a function is a finished result. (Variables
are not values; closed programs never contain free variables anyway.)

    ─────────────
    Value (λ. t)

We use the **call-by-value** strategy (like OCaml, Lean, most languages):
evaluate the function first, then the argument, then call.

        f ⟶ f'
    ─────────────────  (app1)
     f a ⟶ f' a

     Value v     a ⟶ a'
    ─────────────────────  (app2)
       v a ⟶ v a'

          Value v
    ──────────────────────  (beta)
     (λ. t) v ⟶ beta t v

Note that there are no rules for reducing *under* a `λ`: `λ. ((λ.0) (λ.0))`
is a value and does not step.

## Ω, the term that never stops

Recall `ω = λx. x x`. What happens when we apply it to itself?

    Ω = ω ω = (λx. x x) (λx. x x)  ⟶  (λx. x x) (λx. x x) = Ω

It reduces to **itself**, forever. The lambda calculus has non-terminating
programs, and so does every Turing-complete language.

## Your task

1. Implement the executable `step : DTerm → Option DTerm`, returning
   `none` when no rule applies (values and stuck terms). Follow the rules:
   if `f` can step, step it; otherwise if `f` is a lambda and `a` can step,
   step `a`; if both are lambdas, β-reduce.
2. Prove `Step (app idt (app idt idt)) (app idt idt)` (which rule is used
   at the root?).
3. Prove `Step omega omega`.
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

inductive Value : DTerm → Prop
  | lam (t : DTerm) : Value (lam t)

inductive Step : DTerm → DTerm → Prop
  | app1 {f f' a : DTerm} : Step f f' → Step (app f a) (app f' a)
  | app2 {v a a' : DTerm} : Value v → Step a a' → Step (app v a) (app v a')
  | beta {t v : DTerm} : Value v → Step (app (lam t) v) (beta t v)

/-- `λx. x` -/
def idt : DTerm := lam (var 0)

/-- `λx. x x` -/
def omegaFun : DTerm := lam (app (var 0) (var 0))

/-- `Ω = (λx. x x) (λx. x x)` -/
def omega : DTerm := app omegaFun omegaFun

/-! ## Your code -/

/-- One step of call-by-value evaluation, if possible. -/
def step : DTerm → Option DTerm
  | t => sorry

theorem step_app2_example : Step (app idt (app idt idt)) (app idt idt) :=
  sorry

theorem omega_steps_to_itself : Step omega omega :=
  sorry
