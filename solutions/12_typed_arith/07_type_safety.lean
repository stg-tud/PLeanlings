/-
# 12.07 — Type safety

We can now put the pieces together:

    progress:      ⊢ t : T   →   Value t ∨ ∃ t', t ⟶ t'
    preservation:  ⊢ t : T   →   t ⟶ t'   →   ⊢ t' : T

Preservation keeps the program well-typed after every step, and progress
says that a well-typed program is never stuck. By induction on the number
of steps, a well-typed program is not stuck *at any point of its run*:

> **Type safety.** If `⊢ t : T` and `t ⟶* t'`, then `t'` is a value or
> can take another step.

This is Robin Milner's slogan **"well-typed programs cannot go wrong"**,
and it is the central theorem about any typed language. Together with the
type checker from 12.03 we have a complete little story: run `typeOf`, and
if it says `some T`, the program will never hit a run-time type error.

## The dry run for STLC

In chapters 14–16 we prove the very same theorem, with the very same
structure (canonical forms, progress, preservation, safety), for the
simply-typed lambda calculus. What changes is that STLC has *variables*
and *binders*:

* typing judgements get a context: `Γ ⊢ t : T`;
* progress is stated for closed terms (`[] ⊢ t : T`);
* the `β`-step `(λx. t) v ⟶ t[x := v]` performs *substitution*, so
  preservation needs a substitution lemma, which needs weakening, which
  needs renaming... That is where de Bruijn indices come in.

But the skeleton of the proof is exactly what you have just built.

## Your task

1. Prove `preservation_star`: types are preserved along whole runs.
2. Prove `type_safety`.
3. Prove `stuck_untyped`: a stuck term has no type.
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

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

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

/-! ## Exercises -/

theorem preservation_star {t t' : Term} {T : Ty} (ht : HasType t T) (hs : Star Step t t') :
    HasType t' T := by
  induction hs with
  | refl => exact ht
  | step h _ ih => exact ih (preservation ht h)

theorem type_safety {t t' : Term} {T : Ty} (ht : HasType t T) (hs : Star Step t t') :
    Value t' ∨ ∃ t'', Step t' t'' :=
  progress (preservation_star ht hs)

/-- A stuck term (a normal form that is not a value) is ill-typed. -/
theorem stuck_untyped {t : Term} (hnf : ∀ t', ¬ Step t t') (hnv : ¬ Value t) (T : Ty) :
    ¬ HasType t T := by
  intro ht
  rcases progress ht with hv | ⟨t', hs⟩
  · exact hnv hv
  · exact hnf t' hs
