/-
# 14.04 — Substitution

A **substitution** `σ : Nat → Term` assigns a term to every free variable.
`subst σ t` replaces each free `var x` in `t` by `σ x`, all at once
("parallel substitution").

Again the only interesting case is the binder. Under `lam A body`:

* index `0` is the bound variable and must stay `var 0`,
* index `n + 1` is the outer variable `n` and must become `σ n`. But `σ n` is
  now placed *under one more binder*, so its free variables have to be
  shifted by one: `rename Nat.succ (σ n)`.

    exts σ 0       = var 0
    exts σ (n + 1) = rename Nat.succ (σ n)

That shift is precisely what prevents variable capture. Once it is built into
`exts` we never have to think about capture again.

β-reduction substitutes for a single variable. `(λ:A. t) s` reduces to the body
`t` with `var 0` replaced by `s`. The binder disappears, so the *other* free
variables of `t` move down by one:

    subst1 s 0       = s
    subst1 s (n + 1) = var n

We write `t[s]` for `subst (subst1 s) t`. (In TAPL this is `↑⁻¹([0 ↦ ↑¹ s] t)`;
here it is one function.)

Examples:

    subst (subst1 .tru) (.lam .nat (.app (.var 1) (.var 0)))
      = .lam .nat (.app .tru (.var 0))
    -- no capture: the free var 0 that we substitute becomes var 1 under the λ
    subst (subst1 (.var 0)) (.lam .nat (.var 1)) = .lam .nat (.var 1)

## Your task

Define `exts`, the variable and abstraction cases of `subst`, and `subst1`.
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

/-! ## Substitution -/

def exts (σ : Nat → Term) : Nat → Term
  | 0 => sorry
  | n + 1 => sorry

def subst (σ : Nat → Term) : Term → Term
  | .var x => sorry
  | .lam A t => sorry
  | .app f a => .app (subst σ f) (subst σ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .pred t => .pred (subst σ t)
  | .iszero t => .iszero (subst σ t)

def subst1 (s : Term) : Nat → Term
  | 0 => sorry
  | n + 1 => sorry
