/-
# 18.01 — Halting

Chapter 13 showed that untyped λ-terms need not terminate:

    Ω = (λx. x x) (λx. x x)  ⟶  (λx. x x) (λx. x x)  ⟶  …

In STLC, `x x` cannot be typed (`x` would need a type `A` with `A = A ⇒ B`),
and in fact **every closed well-typed program terminates**. This bonus chapter
proves it:

    theorem normalization : HasType [] t T → Halts t

where `Halts t` means that `t` reduces in finitely many steps to a value:

    def Halts (t : Term) : Prop := ∃ v, Star Step t v ∧ Value v

Type safety said "never stuck". Normalization says much more: "always
finishes". (Chapter 17's `fix` breaks this, of course. We'll see in 18.07 exactly
where the proof would fail.)

## A smaller language

To keep the proofs short, this chapter uses STLC with **booleans and
functions only**: no `nat`, `zero`, `succ`, `pred`, `iszero`. Everything else
(de Bruijn terms, typing, parallel substitution, call-by-value `Step`)
is exactly as in chapters 14–16. Natural numbers would only add more cases
of the same kind.

## Why the obvious proof fails

Let's try induction on `HasType [] t T`. Variables can't occur; `lam`, `tru`
and `fls` are values. The case `ite c t e` works: `c` halts with a value,
which is `true` or `false` by canonical forms, and then `t` or `e` halts.
But look at `app f a`. The induction hypotheses say

    f ⟶* lam A b        and        a ⟶* v

so `app f a ⟶* app (lam A b) v ⟶ b[v]`. And now we are stuck: `b[v]` is a
*new* term, not a subterm of `app f a`, and the induction hypotheses say
nothing about it. "`f` halts" is too weak: we need to know that `f`
*applied to a halting argument* halts, and, if the argument is itself a
function, that it does so when applied to halting arguments, and so on. That
stronger, type-indexed property is the **logical relation** of 18.03 (Tait's
method, 1967).

## This file: reduction sequences

We first collect a few facts about `⟶*`:

* `star_trans`: reduction sequences can be concatenated;
* congruence lemmas: `f ⟶* f'` gives `app f a ⟶* app f' a`, and similarly
  for the argument (when the function is a value) and for the condition of `ite`;
* `halts_back`: if `t ⟶ t'` and `t'` halts, so does `t`.

All of them are inductions on the reduction sequence.

## Your task

Prove `star_trans`, `star_app2`, `star_ite` and `halts_back`. The proof of
`star_app1` is a model for the congruence lemmas.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types of this chapter: `T ::= bool | T ⇒ T` (no `nat`). -/
inductive Ty where
  | bool
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
  deriving DecidableEq, Repr

/-- A context lists the types of the free variables: `Γ[0]?` is the type of `var 0`. -/
abbrev Ctx := List Ty

/-- `HasType Γ t T` means `Γ ⊢ t : T`. -/
/-
    Γ[x]? = some A           A :: Γ ⊢ t : B             Γ ⊢ f : A ⇒ B    Γ ⊢ a : A
  ─────────────── var    ──────────────────── lam    ──────────────────────────── app
   Γ ⊢ var x : A          Γ ⊢ lam A t : A ⇒ B                Γ ⊢ app f a : B

  ───────────────── tru   ───────────────── fls
   Γ ⊢ tru : bool          Γ ⊢ fls : bool

   Γ ⊢ c : bool    Γ ⊢ t : A    Γ ⊢ e : A
  ───────────────────────────────────────── ite
          Γ ⊢ ite c t e : A
-/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (.var x) A
  | lam {Γ A t B} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ c t e A} : HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A

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

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions and booleans. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
/-
          Value v                              f ⟶ f'                     Value v    a ⟶ a'
  ──────────────────────────────── beta   ────────────────── app1   ──────────────────────── app2
   app (lam A t) v ⟶ t[v]                  app f a ⟶ app f' a       app v a ⟶ app v a'

  ─────────────────────── iteTrue   ─────────────────────── iteFalse         c ⟶ c'
   ite tru t e ⟶ t                   ite fls t e ⟶ e                  ──────────────────────────── ite
                                                                        ite c t e ⟶ ite c' t e

  where t[v] = subst (subst1 v) t.
-/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)

/-- `t` halts: it reduces in finitely many steps to a value. -/
def Halts (t : Term) : Prop := ∃ v, Star Step t v ∧ Value v

/-! ## Reduction sequences -/

theorem star_trans {t u w : Term} : Star Step t u → Star Step u w → Star Step t w := by
  intro h1 h2
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem star_app1 {f f' a : Term} : Star Step f f' → Star Step (.app f a) (.app f' a) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.app1 h) ih

theorem star_app2 {v a a' : Term} :
    Value v → Star Step a a' → Star Step (.app v a) (.app v a') := by
  intro hv h
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.app2 hv h) ih

theorem star_ite {c c' t e : Term} : Star Step c c' → Star Step (.ite c t e) (.ite c' t e) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.ite h) ih

theorem value_halts {v : Term} : Value v → Halts v :=
  fun hv => ⟨v, .refl v, hv⟩

theorem halts_back {t t' : Term} : Step t t' → Halts t' → Halts t := by
  intro hs h
  obtain ⟨v, hv, hval⟩ := h
  exact ⟨v, .step hs hv, hval⟩

/-- `(λx:bool. x) true` halts: one β-step to the value `true`. -/
example : Halts (.app (.lam .bool (.var 0)) .tru) :=
  ⟨.tru, .step (.beta .tru) (.refl _), .tru⟩
