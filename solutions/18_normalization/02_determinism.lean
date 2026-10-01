/-
# 18.02 — Determinism

In 18.03 we will need that halting is preserved by steps in **both**
directions: if `t ⟶ t'`, then `Halts t ↔ Halts t'`.

* Backwards (`halts_back`, from 18.01) is easy: prepend the step.
* Forwards is not obvious. We know *some* reduction sequence from `t` ends
  in a value. Why should the one through `t'` do the same? In a
  nondeterministic language it need not: `t` could also step to a looping term.

For CBV it is true because reduction is **deterministic**: every term has at
most one next step.

    theorem step_det : Step t t₁ → Step t t₂ → t₁ = t₂

**Proof.** Induction on the first derivation (generalizing `t₂`), then
inversion of the second with `cases`. In each case, either the two rules
match and the induction hypothesis (or `rfl`) closes the goal, or they don't, and
the combination is impossible. Mostly because some value would have to
step, which `value_no_step` refutes:

    theorem value_no_step : Value v → ¬ Step v t

`absurd h (value_no_step hv) : C` turns `h : Step v t` and `hv : Value v` into
a proof of any goal `C`. Sometimes `cases` alone sees the contradiction, e.g. a
step `Step .tru c'` has no matching rule.

With determinism, the unique reduction sequence from `t` to its value must
pass through `t'`:

    theorem star_step_det : Star Step t v → Value v → Step t t' → Star Step t' v

(the sequence `t ⟶* v` is not empty, because a value can't step; so it starts
with a step `t ⟶ t''`, and `t'' = t'`). Forward preservation of halting follows.

## Your task

1. Prove `value_no_step`. (`cases hv <;> cases hs` tries all combinations.)
2. Fill in the `app2` and `ite` cases of `step_det`.
3. Prove `star_step_det` and `halts_fwd`.
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

/-! ## Determinism -/

theorem value_no_step {v t : Term} : Value v → ¬ Step v t := by
  intro hv hs
  cases hv <;> cases hs

theorem step_det {t t₁ t₂ : Term} : Step t t₁ → Step t t₂ → t₁ = t₂ := by
  intro h1 h2
  induction h1 generalizing t₂ with
  | beta hv =>
    cases h2 with
    | beta _ => rfl
    | app1 h => cases h
    | app2 _ h => exact absurd h (value_no_step hv)
  | app1 h ih =>
    cases h2 with
    | beta _ => cases h
    | app1 h' => rw [ih h']
    | app2 hv _ => exact absurd h (value_no_step hv)
  | app2 hv h ih =>
    cases h2 with
    | beta hv' => exact absurd h (value_no_step hv')
    | app1 h' => exact absurd h' (value_no_step hv)
    | app2 _ h' => rw [ih h']
  | iteTrue =>
    cases h2 with
    | iteTrue => rfl
    | ite h => cases h
  | iteFalse =>
    cases h2 with
    | iteFalse => rfl
    | ite h => cases h
  | ite h ih =>
    cases h2 with
    | iteTrue => cases h
    | iteFalse => cases h
    | ite h' => rw [ih h']

theorem star_step_det {t t' v : Term} :
    Star Step t v → Value v → Step t t' → Star Step t' v := by
  intro hs hv h
  cases hs with
  | refl => exact absurd h (value_no_step hv)
  | step h' rest =>
    rw [step_det h h']
    exact rest

theorem halts_fwd {t t' : Term} : Step t t' → Halts t → Halts t' := by
  intro hs h
  obtain ⟨v, hv, hval⟩ := h
  exact ⟨v, star_step_det hv hval hs, hval⟩
