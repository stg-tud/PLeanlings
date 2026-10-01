/-
# 18.03 — The logical relation

We now strengthen "halts" to a property that survives application.
**Reducibility** `R T t` is defined by recursion on the *type* `T`:

    R bool t     :=  t ⟶* true  ∨  t ⟶* false
    R (A ⇒ B) t  :=  Halts t  ∧  ∀ s, R A s → R B (app t s)

A function is reducible if it halts and maps reducible arguments to reducible
results. That is exactly the induction hypothesis the `app` case in 18.01
was missing. Relations of this shape, defined by recursion on types with
functions mapping related arguments to related results, are called **logical
relations**. They are a central tool in PL theory: besides normalization, they
prove parametricity ("theorems for free"), contextual equivalence of programs,
and compiler correctness.

Two remarks on the definition:

* It is a `def` by **structural recursion on `Ty`**, not an `inductive`. An inductive
  definition would mention `R A s` to the *left* of an arrow in a
  constructor (`(∀ s, R A s → R B (app t s)) → R (A ⇒ B) t`). That is a *negative
  occurrence*, and Lean rejects it. Recursion on the type is fine, because
  `A` and `B` are smaller than `A ⇒ B`. Since `R` is a `def`, `R (A ⇒ B) t` *is*
  the conjunction by definition: `h.1`, `h.2` and `⟨_, _⟩` work directly.
* Unlike Software Foundations, our `R` does not contain `HasType [] t T`.
  SF needs the typing to get canonical forms at `bool`; we built them into
  `R bool` instead ("reduces to `true` or `false`"), and nothing else
  needs typing. So we never need preservation in this chapter.

## Properties of `R`

* `R_halts`: reducible terms halt. (By definition at `⇒`; at `bool` the
  booleans are values.)
* `R` is closed under steps in both directions: if `t ⟶ t'`, then
  `R T t ↔ R T t'`. By induction on `T`. At `bool` use the lemmas about
  `Star`. At `A ⇒ B` use `halts_back`/`halts_fwd` for the first component;
  for the second, `app t s ⟶ app t' s` (rule `app1`) and the induction hypothesis for `B`.
* The multi-step versions follow by induction on `⟶*`.

The backward direction is given as a model; you do the forward one.

## Your task

Prove `R_halts`, `R_fwd` and `R_star_fwd`. Look at `R_back` and
`R_star_back` first.
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

/-! ## Reducibility -/

/-- The logical relation ("reducibility"), by recursion on the type:

* `R bool t`: `t` reduces to `true` or to `false`;
* `R (A ⇒ B) t`: `t` halts, and applied to any `R A` argument it gives an `R B` result. -/
def R : Ty → Term → Prop
  | .bool, t => Star Step t .tru ∨ Star Step t .fls
  | .arrow A B, t => Halts t ∧ ∀ s, R A s → R B (.app t s)

/-- `true` is reducible at `bool`. `R .bool .tru` unfolds by definition, so the
anonymous constructor and `Or.inl` see through it. -/
example : R .bool .tru := Or.inl (.refl _)

/-- The identity on booleans is reducible at `bool ⇒ bool`. -/
example : R (.bool ⇒ .bool) (.lam .bool (.var 0)) := by
  refine ⟨value_halts .lam, fun s hs => ?_⟩
  -- `hs : R .bool s`, i.e. `s` reduces to `true` or `false`. Then
  -- `(λx. x) s ⟶* (λx. x) b ⟶ b` for that boolean `b`.
  rcases hs with h | h
  · exact Or.inl (star_trans (star_app2 .lam h) (.step (.beta .tru) (.refl _)))
  · exact Or.inr (star_trans (star_app2 .lam h) (.step (.beta .fls) (.refl _)))

theorem R_halts {T : Ty} {t : Term} : R T t → Halts t := by
  sorry

theorem R_back {T : Ty} {t t' : Term} : Step t t' → R T t' → R T t := by
  intro hs h
  induction T generalizing t t' with
  | bool =>
    rcases h with h | h
    · exact Or.inl (.step hs h)
    · exact Or.inr (.step hs h)
  | arrow A B _ ihB =>
    exact ⟨halts_back hs h.1, fun s hRs => ihB (.app1 hs) (h.2 s hRs)⟩

theorem R_fwd {T : Ty} {t t' : Term} : Step t t' → R T t → R T t' := by
  sorry

theorem R_star_back {T : Ty} {t t' : Term} : Star Step t t' → R T t' → R T t := by
  intro hs h
  induction hs with
  | refl => exact h
  | step h1 _ ih => exact R_back h1 (ih h)

theorem R_star_fwd {T : Ty} {t t' : Term} : Star Step t t' → R T t → R T t' := by
  sorry
