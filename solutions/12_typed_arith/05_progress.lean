/-
# 12.05 — Progress

The first half of type safety:

> **Progress.** A well-typed term is not stuck: either it is a value, or
> it can take a step.

    ⊢ t : T   →   Value t ∨ ∃ t', t ⟶ t'

The proof is by induction on the typing derivation. Look at the `pred`
case: we know `⊢ t : Nat` and, by induction, `t` is a value or steps.

* If `t ⟶ t'`, then `pred t ⟶ pred t'` by the congruence rule.
* If `t` is a value, canonical forms says that `t` is a numeric value:
  either `0` (step with `predZero`) or `succ v` with `NValue v` (step with
  `predSucc`).

Note how the typing assumption is used exactly once, in the canonical forms
lemma, to exclude the stuck case `pred true`.

Useful Lean idioms:
* `rcases ih with hv | ⟨t', hs⟩` splits the induction hypothesis.
* `rcases canonical_bool hv hc with rfl | rfl` splits on `c = true ∨
  c = false` and substitutes `c` right away.
* `exact ⟨_, Step.predZero⟩` proves an `∃ t', Step … t'`; Lean infers the
  witness from the rule.

## Your task

Complete the `ite`, `pred` and `iszero` cases.
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

theorem canonical_bool {v : Term} (hv : Value v) (ht : HasType v .bool) :
    v = .tru ∨ v = .fls := by
  cases hv with
  | tru => left; rfl
  | fls => right; rfl
  | nv hn => cases hn <;> cases ht

theorem canonical_nat {v : Term} (hv : Value v) (ht : HasType v .nat) : NValue v := by
  cases hv with
  | tru => cases ht
  | fls => cases ht
  | nv hn => exact hn

/-! ## Exercises -/

theorem progress {t : Term} {T : Ty} (ht : HasType t T) : Value t ∨ ∃ t', Step t t' := by
  induction ht with
  | tru => left; exact Value.tru
  | fls => left; exact Value.fls
  | zero => left; exact Value.nv NValue.zero
  | ite hc _ _ ihc _ _ =>
    right
    rcases ihc with hv | ⟨c', hs⟩
    · rcases canonical_bool hv hc with rfl | rfl
      · exact ⟨_, Step.iteTrue⟩
      · exact ⟨_, Step.iteFalse⟩
    · exact ⟨_, Step.ite hs⟩
  | succ ht ih =>
    rcases ih with hv | ⟨t', hs⟩
    · left
      exact Value.nv (NValue.succ (canonical_nat hv ht))
    · right
      exact ⟨_, Step.succ hs⟩
  | pred ht ih =>
    right
    rcases ih with hv | ⟨t', hs⟩
    · cases canonical_nat hv ht with
      | zero => exact ⟨_, Step.predZero⟩
      | succ hn => exact ⟨_, Step.predSucc hn⟩
    · exact ⟨_, Step.pred hs⟩
  | iszero ht ih =>
    right
    rcases ih with hv | ⟨t', hs⟩
    · cases canonical_nat hv ht with
      | zero => exact ⟨_, Step.iszeroZero⟩
      | succ hn => exact ⟨_, Step.iszeroSucc hn⟩
    · exact ⟨_, Step.iszero hs⟩
