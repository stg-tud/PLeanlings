/-
# 12.06 — Preservation

The second half of type safety:

> **Preservation** (also called *subject reduction*). Taking a step does
> not change the type.

    ⊢ t : T    t ⟶ t'
    ─────────────────
        ⊢ t' : T

We prove it by induction on the step `t ⟶ t'` (generalizing `T`), and in
each case invert the typing derivation of `t` with `cases ht`. Because the
typing rules are syntax-directed, inversion yields exactly one case, with
the typing derivations of the subterms. For example, in the `iteTrue` case,
`t = if true then t₁ else t₂`, and `cases ht` gives us `⊢ t₁ : T`, which is
just what we need.

The most interesting case is `predSucc`: from `⊢ pred (succ v) : T` we get
`T = Nat` and `⊢ succ v : Nat`, and inverting once more gives `⊢ v : Nat`.

## Your task

Fill in the missing cases.

(Preservation is where STLC gets harder: the `β`-rule
`(λx. t) v ⟶ t[x := v]` creates a new term by *substitution*, so we will
first need a lemma that substitution preserves types. Here, every step
only rearranges existing subterms.)
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Term where
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving Repr, DecidableEq

inductive NValue : Term → Prop
  | zero : NValue .zero
  | succ {v : Term} : NValue v → NValue (.succ v)

inductive Value : Term → Prop
  | tru : Value .tru
  | fls : Value .fls
  | nv {v : Term} : NValue v → Value v

/-
**Computation rules** (where the actual work happens):

    ─────────────────────────── iteTrue    ──────────────────────────── iteFalse
    if true then t else e ⟶ t              if false then t else e ⟶ e

    ─────────── predZero          NValue v
    pred 0 ⟶ 0               ─────────────────── predSucc
                              pred (succ v) ⟶ v

    ──────────────── iszeroZero        NValue v
    iszero 0 ⟶ true              ──────────────────────── iszeroSucc
                                  iszero (succ v) ⟶ false

**Congruence rules** (where to look for the next step):

                  c ⟶ c'                                t ⟶ t'
    ──────────────────────────────────────── ite    ───────────────── succ
    if c then t else e ⟶ if c' then t else e        succ t ⟶ succ t'

          t ⟶ t'                       t ⟶ t'
    ───────────────── pred    ───────────────────── iszero
    pred t ⟶ pred t'          iszero t ⟶ iszero t'
-/
inductive Step : Term → Term → Prop
  | iteTrue {t e : Term} : Step (.ite .tru t e) t
  | iteFalse {t e : Term} : Step (.ite .fls t e) e
  | ite {c c' t e : Term} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t' : Term} : Step t t' → Step (.succ t) (.succ t')
  | predZero : Step (.pred .zero) .zero
  | predSucc {v : Term} : NValue v → Step (.pred (.succ v)) v
  | pred {t t' : Term} : Step t t' → Step (.pred t) (.pred t')
  | iszeroZero : Step (.iszero .zero) .tru
  | iszeroSucc {v : Term} : NValue v → Step (.iszero (.succ v)) .fls
  | iszero {t t' : Term} : Step t t' → Step (.iszero t) (.iszero t')

inductive Ty where
  | bool
  | nat
  deriving Repr, DecidableEq

/-

    ─────────────── tru     ─────────────── fls     ────────────── zero
    ⊢ true : Bool           ⊢ false : Bool          ⊢ 0 : Nat

    ⊢ c : Bool    ⊢ t : T    ⊢ e : T
    ───────────────────────────────── ite
       ⊢ if c then t else e : T

      ⊢ t : Nat                ⊢ t : Nat                 ⊢ t : Nat
    ───────────────── succ   ───────────────── pred   ──────────────────── iszero
    ⊢ succ t : Nat           ⊢ pred t : Nat           ⊢ iszero t : Bool
-/
inductive HasType : Term → Ty → Prop
  | tru : HasType .tru .bool
  | fls : HasType .fls .bool
  | ite {c t e : Term} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
  | zero : HasType .zero .nat
  | succ {t : Term} : HasType t .nat → HasType (.succ t) .nat
  | pred {t : Term} : HasType t .nat → HasType (.pred t) .nat
  | iszero {t : Term} : HasType t .nat → HasType (.iszero t) .bool

/-! ## Exercises -/

theorem preservation {t t' : Term} {T : Ty} (ht : HasType t T) (hs : Step t t') :
    HasType t' T := by
  induction hs generalizing T with
  | iteTrue =>
    cases ht with
    | ite _ h₁ _ => exact h₁
  | iteFalse =>
    cases ht with
    | ite _ _ h₂ => exact h₂
  | ite _ ih =>
    cases ht with
    | ite hc h₁ h₂ => exact HasType.ite (ih hc) h₁ h₂
  | succ _ ih =>
    cases ht with
    | succ h => exact HasType.succ (ih h)
  | predZero =>
    cases ht
    exact HasType.zero
  | predSucc _ =>
    cases ht with
    | pred h =>
      cases h with
      | succ h' => exact h'
  | pred _ ih =>
    cases ht with
    | pred h => exact HasType.pred (ih h)
  | iszeroZero =>
    cases ht
    exact HasType.tru
  | iszeroSucc _ =>
    cases ht
    exact HasType.fls
  | iszero _ ih =>
    cases ht with
    | iszero h => exact HasType.iszero (ih h)
