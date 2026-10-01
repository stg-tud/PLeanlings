/-
# 14.07 — An interpreter

`Step` is a relation. Here is its executable counterpart:

    step : Term → Option Term

`step t = some t'` means "`t` takes one step to `t'`", and `none` means that `t` is a
value or stuck. A boolean version of `Value`, `isValue`, tells us which of
the CBV rules applies. For an application `app f a`:

* if `f` is not a value, reduce `f` (rule `app1`),
* else if `a` is not a value, reduce `a` (rule `app2`),
* else, if `f` is an abstraction `lam _ t`, β-reduce to `t[a]`; otherwise we
  are stuck.

`Option.map` is handy here: `(step f).map (.app · a)` turns `some f'` into
`some (.app f' a)` and leaves `none` alone.

Since STLC has no recursion, every well-typed program terminates (you
can prove that in bonus chapter 18!). Still, a *Lean* function must be total,
so `eval` takes **fuel**: the maximum number of steps to take.

    eval 0       t = t
    eval (n + 1) t = eval n t'   if step t = some t'
                   = t           if step t = none

A pretty printer is provided, which names variables after the depth of their binder
(`x0` is bound by the outermost `λ`) and prints numerals as digits.

## Your task

1. Write the `app` case of `step`.
2. Define `eval`.

Then uncomment the demos at the end and run some programs. Note how
`twice (nat ⇒ nat) (twice nat) succFn 0` computes `4`: we cannot write a
polymorphic `twice` inside STLC, so we use a Lean function to generate one copy
per type.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Types: `T ::= bool | nat | T ⇒ T`. -/
inductive Ty where
  | bool
  | nat
  | arrow (A B : Ty)
  deriving DecidableEq

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
  deriving DecidableEq

/-- Lift a renaming under a binder: `0` stays `0`, `n + 1` becomes `ρ n + 1`. -/
def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply the renaming `ρ` to all free variables. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .var x => .var (ρ x)
  | .lam A t => .lam A (rename (ext ρ) t)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .pred t => .pred (rename ρ t)
  | .iszero t => .iszero (rename ρ t)

/-- Lift a substitution under a binder. -/
def exts (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Parallel substitution: replace every free variable `x` by `σ x`. -/
def subst (σ : Nat → Term) : Term → Term
  | .var x => σ x
  | .lam A t => .lam A (subst (exts σ) t)
  | .app f a => .app (subst σ f) (subst σ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .pred t => .pred (subst σ t)
  | .iszero t => .iszero (subst σ t)

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Pretty printing. Variables are named after the depth of their binder,
so `lam .nat (lam .nat (var 1))` prints as `(λx0 : nat. (λx1 : nat. x0))`. -/
def Ty.pretty : Ty → String
  | .bool => "bool"
  | .nat => "nat"
  | .arrow (.arrow A B) C => s!"({(Ty.arrow A B).pretty}) ⇒ {C.pretty}"
  | .arrow A B => s!"{A.pretty} ⇒ {B.pretty}"

def Term.toNat? : Term → Option Nat
  | .zero => some 0
  | .succ t => t.toNat?.map (· + 1)
  | _ => none

def Term.pretty (depth : Nat) : Term → String
  | .var x => if x < depth then s!"x{depth - 1 - x}" else s!"#{x}"
  | .lam A t => s!"(λx{depth} : {A.pretty}. {t.pretty (depth + 1)})"
  | .app f a => s!"({f.pretty depth} {a.pretty depth})"
  | .tru => "true"
  | .fls => "false"
  | .ite c t e => s!"(if {c.pretty depth} then {t.pretty depth} else {e.pretty depth})"
  | .zero => "0"
  | .succ t =>
    match t.toNat? with
    | some n => toString (n + 1)
    | none => s!"(succ {t.pretty depth})"
  | .pred t => s!"(pred {t.pretty depth})"
  | .iszero t => s!"(iszero {t.pretty depth})"

instance : Repr Ty where
  reprPrec T p := match T with
    | .arrow _ _ => Repr.addAppParen T.pretty p
    | _ => T.pretty
instance : Repr Term := ⟨fun t _ => t.pretty 0⟩

/-- The numeral `n` as a term: `succ (succ … zero)`. -/
def Term.num : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (Term.num n)

/-! ## Programs -/

/-- `λx:nat. succ x` -/
def succFn : Term := .lam .nat (.succ (.var 0))

/-- `λb:bool. if b then false else true` -/
def notFn : Term := .lam .bool (.ite (.var 0) .fls .tru)

/-- `λf:A⇒A. λx:A. f (f x)`, one copy for every type `A`. -/
def twice (A : Ty) : Term := .lam (A ⇒ A) (.lam A (.app (.var 1) (.app (.var 1) (.var 0))))

/-! ## The interpreter -/

/-- Executable version of `Value`. -/
def isValue : Term → Bool
  | .lam _ _ => true
  | .tru => true
  | .fls => true
  | .zero => true
  | .succ t => isValue t
  | _ => false

def step : Term → Option Term
  | .app f a =>
    if isValue f then
      if isValue a then
        match f with
        | .lam _ t => some (subst (subst1 a) t)
        | _ => none
      else (step a).map (.app f ·)
    else (step f).map (.app · a)
  | .ite c t e =>
    if isValue c then
      match c with
      | .tru => some t
      | .fls => some e
      | _ => none
    else (step c).map (.ite · t e)
  | .succ t => (step t).map .succ
  | .pred t =>
    if isValue t then
      match t with
      | .zero => some .zero
      | .succ v => some v
      | _ => none
    else (step t).map .pred
  | .iszero t =>
    if isValue t then
      match t with
      | .zero => some .tru
      | .succ _ => some .fls
      | _ => none
    else (step t).map .iszero
  | _ => none

def eval : Nat → Term → Term
  | 0, t => t
  | n + 1, t =>
    match step t with
    | some t' => eval n t'
    | none => t

/-! ## Demos -/

#eval twice .nat
#eval eval 100 (.app (.app (twice .nat) succFn) .zero)
#eval eval 100 (.app (.app (.app (twice (.nat ⇒ .nat)) (twice .nat)) succFn) .zero)
#eval eval 100 (.app notFn (.app notFn .tru))
#eval eval 100 (.app (.app (twice .bool) notFn) .fls)
-- A stuck (ill-typed) program stays where it is:
#eval eval 100 (.app .tru .zero)
