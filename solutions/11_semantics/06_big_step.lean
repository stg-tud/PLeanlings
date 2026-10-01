/-
# 11.06 — Big-step semantics

Small-step semantics describes every single step. A **big-step** (or
*natural*) semantics instead relates a term directly to its final value:
`t ⇓ v`, "`t` evaluates to `v`". It is the inference-rule version of a
recursive interpreter like `eval` from chapter 10.

       Value v               c ⇓ true    t ⇓ v              c ⇓ false    e ⇓ v
    ───────────── val     ─────────────────────── iteTrue  ─────────────────────── iteFalse
        v ⇓ v             if c then t else e ⇓ v           if c then t else e ⇓ v

      t ⇓ v    NValue v                 t ⇓ 0              t ⇓ succ v    NValue v
    ───────────────────── succ    ──────────── predZero    ───────────────────── predSucc
     succ t ⇓ succ v               pred t ⇓ 0                  pred t ⇓ v

         t ⇓ 0                         t ⇓ succ v    NValue v
    ───────────────── iszeroZero    ────────────────────────── iszeroSucc
    iszero t ⇓ true                    iszero t ⇓ false

Two semantics for one language: we had better prove that they agree! Here
we show one direction: whatever big-step evaluation computes is also
reached by a small-step run.

    t ⇓ v   →   t ⟶* v

The proof is by induction on `t ⇓ v`. Take `iteTrue`: by induction,
`c ⟶* true` and `t ⟶* v`. Glue together a run

    if c then t else e  ⟶*  if true then t else e     (star_ite)
                        ⟶   t                          (Step.iteTrue)
                        ⟶*  v                          (induction hypothesis)

with `Star.trans` and `Star.step`. The congruence lemmas from the previous
exercise are given below.

(The other direction, `t ⟶* v → Value v → t ⇓ v`, holds too, but needs a
bit more work. Try it if you want an extra challenge!)

## Your task

Fill in the missing cases of `eval_star`.
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

theorem Star.single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
  .step h (.refl b)

theorem Star.trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₁ with
  | refl => exact h₂
  | step hab _ ih => exact .step hab (ih h₂)

theorem Star.lift {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {a b : α}, R a b → S (f a) (f b))
    {a b : α} (h : Star R a b) : Star S (f a) (f b) := by
  induction h with
  | refl => exact Star.refl _
  | step hab _ ih => exact Star.step (hf hab) ih

theorem star_succ {t t' : Term} (h : Star Step t t') : Star Step (.succ t) (.succ t') :=
  Star.lift Term.succ Step.succ h

theorem star_ite {c c' : Term} (t e : Term) (h : Star Step c c') :
    Star Step (.ite c t e) (.ite c' t e) :=
  Star.lift (fun c => Term.ite c t e) Step.ite h

theorem star_pred {t t' : Term} (h : Star Step t t') : Star Step (.pred t) (.pred t') :=
  Star.lift Term.pred Step.pred h

theorem star_iszero {t t' : Term} (h : Star Step t t') : Star Step (.iszero t) (.iszero t') :=
  Star.lift Term.iszero Step.iszero h

/-- Big-step evaluation `t ⇓ v`. -/
inductive Eval : Term → Term → Prop
  | val {v : Term} : Value v → Eval v v
  | iteTrue {c t e v : Term} : Eval c .tru → Eval t v → Eval (.ite c t e) v
  | iteFalse {c t e v : Term} : Eval c .fls → Eval e v → Eval (.ite c t e) v
  | succ {t v : Term} : Eval t v → NValue v → Eval (.succ t) (.succ v)
  | predZero {t : Term} : Eval t .zero → Eval (.pred t) .zero
  | predSucc {t v : Term} : Eval t (.succ v) → NValue v → Eval (.pred t) v
  | iszeroZero {t : Term} : Eval t .zero → Eval (.iszero t) .tru
  | iszeroSucc {t v : Term} : Eval t (.succ v) → NValue v → Eval (.iszero t) .fls

/-! ## Exercises -/

theorem eval_star {t v : Term} (h : Eval t v) : Star Step t v := by
  induction h with
  | val _ => exact Star.refl _
  | iteTrue _ _ ihc iht =>
    exact Star.trans (star_ite _ _ ihc) (Star.step Step.iteTrue iht)
  | iteFalse _ _ ihc ihe =>
    exact Star.trans (star_ite _ _ ihc) (Star.step Step.iteFalse ihe)
  | succ _ _ ih =>
    exact star_succ ih
  | predZero _ ih =>
    exact Star.trans (star_pred ih) (Star.single Step.predZero)
  | predSucc _ hv ih =>
    exact Star.trans (star_pred ih) (Star.single (Step.predSucc hv))
  | iszeroZero _ ih =>
    exact Star.trans (star_iszero ih) (Star.single Step.iszeroZero)
  | iszeroSucc _ hv ih =>
    exact Star.trans (star_iszero ih) (Star.single (Step.iszeroSucc hv))
