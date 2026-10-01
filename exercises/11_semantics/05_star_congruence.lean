/-
# 11.05 — Congruence for multi-step reduction

The congruence rules say: if `c ⟶ c'`, then
`if c then t else e ⟶ if c' then t else e`. Next we want the same for
*runs*: if `c ⟶* c'` in many steps, then the whole `if` gets there in
just as many steps, by wrapping every single step in `Step.ite`:

          c ⟶* c'
    ─────────────────────────────────────────
    if c then t else e ⟶* if c' then t else e

We need four such lemmas (for `ite`, `succ`, `pred`, `iszero`) and they all
have the same proof. So let's prove it *once*, in general: whenever a
function `f` maps single `R`-steps to single `S`-steps, it maps `R`-runs to
`S`-runs.

    ∀ a b, R a b → S (f a) (f b)        Star R a b
    ──────────────────────────────────────────────── Star.lift
                  Star S (f a) (f b)

(The function `f` describes the context the steps happen in, e.g.
`f = fun c => .ite c t e`. In the jargon: an *evaluation context*.)

Then each concrete lemma is an instance, e.g.

    theorem star_succ … := Star.lift Term.succ Step.succ h

## Your task

1. Prove `Star.lift` by induction on the run `h`.
2. Prove the congruence lemmas `star_ite`, `star_pred` and `star_iszero`
   using `Star.lift`.
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

/-! ## Exercises -/

theorem Star.lift {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {a b : α}, R a b → S (f a) (f b))
    {a b : α} (h : Star R a b) : Star S (f a) (f b) := by
  sorry

theorem star_succ {t t' : Term} (h : Star Step t t') :
    Star Step (.succ t) (.succ t') :=
  Star.lift Term.succ Step.succ h

theorem star_ite {c c' : Term} (t e : Term) (h : Star Step c c') :
    Star Step (.ite c t e) (.ite c' t e) :=
  sorry

theorem star_pred {t t' : Term} (h : Star Step t t') :
    Star Step (.pred t) (.pred t') :=
  sorry

theorem star_iszero {t t' : Term} (h : Star Step t t') :
    Star Step (.iszero t) (.iszero t') :=
  sorry
