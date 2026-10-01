/-
# 13.06 — An interpreter with fuel

Repeating `step` until no rule applies gives an **interpreter**:

    eval t = if t ⟶ t' then eval t' else t

But we cannot write this in Lean as is! Lean insists that every function
**terminates** on every input. That is not pedantry: Lean is also a logic,
and a non-terminating definition like

    def loop (n : Nat) : False := loop n

would "prove" `False`. Lean only accepts recursion it can see terminates
(e.g. structural recursion on a smaller argument). Our `eval` cannot pass
that test, and for good reason — `eval Ω` really runs forever.

(`partial def` lets you write it anyway, but then Lean treats the function
as opaque and you can prove nothing about it.)

The standard trick is **fuel**: an extra `Nat` argument that decreases on
each step. Out of fuel? Give up and return `none`.

    eval 0       t = none                          (out of fuel)
    eval (n + 1) t = eval n t'     if step t = some t'
                   = some t        if step t = none  (t is a normal form)

Now the recursion is structural on the fuel, and Lean is happy. A result
`some t` means "terminated with `t`" (a value, or a stuck term); `none`
means "didn't finish in time" — which for Ω happens **for every amount of
fuel**, the formal counterpart of "Ω diverges".

## Your task

1. Implement `eval` as above.
2. Prove `eval_omega : ∀ n, eval n omega = none` by induction on `n`.
   You may need the fact `step omega = some omega`, which holds by `rfl`.
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

def step : DTerm → Option DTerm
  | app (lam t) (lam s) => some (beta t (lam s))
  | app (lam t) a => (step a).map (fun a' => app (lam t) a')
  | app f a => (step f).map (fun f' => app f' a)
  | _ => none

/-- `λx. λy. x` -/
def K : DTerm := lam (lam (var 1))

/-! ## Your code -/

/-- Run call-by-value evaluation for at most `fuel` steps. -/
def eval : Nat → DTerm → Option DTerm
  | 0, _ => none
  | n + 1, t =>
    match step t with
    | some t' => eval n t'
    | none => some t

theorem eval_omega : ∀ n, eval n omega = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : step omega = some omega := rfl
    simp only [eval, h]
    exact ih

#eval eval 10 (app (app K idt) omegaFun)   -- some idt
#eval eval 1000 omega                      -- none
