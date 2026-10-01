/-
# 14.05 — Call-by-value reduction

Values are the results of computation: abstractions, booleans and numerals.

    ───────────────    ─────────    ─────────    ──────────        Value v
     Value (lam A t)    Value tru    Value fls    Value zero    ────────────────
                                                                 Value (succ v)

Evaluation is **call-by-value** (CBV), left to right: in `app f a` first reduce
`f` to a value, then `a`, and only then β-reduce. We never reduce under a
`λ`: an abstraction is already a value.

          Value v                              f ⟶ f'                     Value v    a ⟶ a'
  ──────────────────────────────── beta   ────────────────── app1   ──────────────────────── app2
   app (lam A t) v ⟶ t[v]                  app f a ⟶ app f' a       app v a ⟶ app v a'

where `t[v]` is `subst (subst1 v) t`. The rules for booleans and numbers are those of
chapter 11 (see the definition below).

A concrete reduction is proved by naming the rule: for instance
`Step.beta Value.tru : Step (.app (.lam .bool (.var 0)) .tru) (subst (subst1 .tru) (.var 0))`,
and Lean accepts it at type `Step (.app (.lam .bool (.var 0)) .tru) .tru`,
since `subst (subst1 .tru) (.var 0)` *computes* to `.tru`.

Some terms are **stuck**: they are not values, but no rule applies, e.g.
`app tru zero`. Type safety (chapter 15) says that well-typed terms never get stuck.

## Your task

1. `step_beta` and `run_const`: prove the concrete reductions.
2. `value_no_step`: values do not reduce (induction on `Value`).
3. `stuck_example`: `app tru zero` is stuck.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

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

/-! ## Values and reduction -/

/-- Values: λ-abstractions, booleans and numerals. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls
  | zero : Value .zero
  | succ {v} : Value v → Value (.succ v)

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
/-
          Value v                              f ⟶ f'                     Value v    a ⟶ a'
  ──────────────────────────────── beta   ────────────────── app1   ──────────────────────── app2
   app (lam A t) v ⟶ t[v]                  app f a ⟶ app f' a       app v a ⟶ app v a'

  ─────────────────────── iteTrue   ─────────────────────── iteFalse         c ⟶ c'
   ite tru t e ⟶ t                   ite fls t e ⟶ e                  ──────────────────────────── ite
                                                                        ite c t e ⟶ ite c' t e
       t ⟶ t'                                               Value v                    t ⟶ t'
  ─────────────────── succ  ───────────────── predZero  ──────────────────── predSucc  ─────────────────── pred
   succ t ⟶ succ t'          pred zero ⟶ zero           pred (succ v) ⟶ v              pred t ⟶ pred t'

                                       Value v                            t ⟶ t'
  ───────────────────── iszeroZero  ───────────────────────── iszeroSucc  ─────────────────────── iszero
   iszero zero ⟶ tru                 iszero (succ v) ⟶ fls               iszero t ⟶ iszero t'

  where t[v] = subst (subst1 v) t.
-/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t'} : Step t t' → Step (.succ t) (.succ t')
  | predZero : Step (.pred .zero) .zero
  | predSucc {v} : Value v → Step (.pred (.succ v)) v
  | pred {t t'} : Step t t' → Step (.pred t) (.pred t')
  | iszeroZero : Step (.iszero .zero) .tru
  | iszeroSucc {v} : Value v → Step (.iszero (.succ v)) .fls
  | iszero {t t'} : Step t t' → Step (.iszero t) (.iszero t')

-- `(λx:bool. x) true ⟶ true`
example : Step (.app (.lam .bool (.var 0)) .tru) .tru := Step.beta Value.tru

-- `(λx:nat. succ x) 0 ⟶ succ 0`
theorem step_beta : Step (.app (.lam .nat (.succ (.var 0))) .zero) (.succ .zero) :=
  Step.beta Value.zero

-- `(λx:bool. λy:nat. x) true (pred 0) ⟶* true`
theorem run_const :
    Star Step (.app (.app (.lam .bool (.lam .nat (.var 1))) .tru) (.pred .zero)) .tru := by
  apply Star.step (Step.app1 (Step.beta Value.tru))
  apply Star.step (Step.app2 Value.lam Step.predZero)
  apply Star.step (Step.beta Value.zero)
  exact Star.refl _

theorem value_no_step {v t : Term} : Value v → ¬ Step v t := by
  intro hv
  induction hv generalizing t with
  | succ _ ih =>
    intro hs
    cases hs with
    | succ hs' => exact ih hs'
  | _ =>
    intro hs
    cases hs

theorem stuck_example : ¬ Value (.app .tru .zero) ∧ ∀ t, ¬ Step (.app .tru .zero) t := by
  constructor
  · intro h
    cases h
  · intro t h
    cases h with
    | app1 h => cases h
    | app2 _ h => cases h
