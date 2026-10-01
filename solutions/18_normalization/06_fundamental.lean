/-
# 18.06 — The fundamental lemma

A substitution `σ` is an **instantiation** of `Γ` if it replaces every
variable of `Γ` by a reducible term of its type:

    def Inst (Γ : Ctx) (σ : Nat → Term) : Prop := ∀ x A, Γ[x]? = some A → R A (σ x)

**Fundamental lemma.** Every well-typed term is reducible, once its free
variables are instantiated:

    theorem fundamental : HasType Γ t T → Inst Γ σ → R T (subst σ t)

The generalization to open terms and all `σ` is essential, because the body of a `λ` is
open. **Proof** by induction on the typing derivation, generalizing `σ`:

* `var x`: `subst σ (var x) = σ x`, reducible by `Inst`.
* `app f a`: the induction hypothesis for `f` is `R (A ⇒ B) (subst σ f)`, whose
  second component, applied to the induction hypothesis for `a`, is the goal. *This* is
  the case that broke in 18.01, and here it is one line.
* `tru`, `fls`: they reduce to themselves in zero steps.
* `ite c t e`: the induction hypothesis for `c` says `subst σ c ⟶* true` or `⟶* false`.
  In the first case, `ite (subst σ c) … ⟶* ite true … ⟶ subst σ t`, which is
  reducible by the induction hypothesis for `t`. Use `R_star_back`, `star_trans`, `star_ite`.
* `lam A t`: we must show `R (A ⇒ B) (lam A (subst (exts σ) t))`.
  1. It halts: it is a value.
  2. Let `s` with `R A s`. By `R_halts`, `s ⟶* v` for a value `v`, and `R A v` by
     `R_star_fwd`. So `scons v σ` instantiates `A :: Γ` (`inst_cons`), and
     the induction hypothesis gives `R B (subst (scons v σ) t)`.
  3. Rewrite with `subst1_exts` (from right to left) to get
     `R B (subst (subst1 v) (subst (exts σ) t))`.
  4. Finally, the application `app (lam A …) s ⟶* app (lam A …) v ⟶ subst (subst1 v) (…)`,
     so `R_star_back` (with `star_app2`) and `R_back` (with `Step.beta`) finish the job.

    refine ⟨value_halts .lam, fun s hs => ?_⟩   -- splits the goal at ⇒

## Your task

1. Prove `inst_cons` (a case distinction on the variable, like `ext_ok`/`exts_ok` in 15).
2. Fill in the `lam` and `ite` cases of `fundamental`.
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

/-- The logical relation ("reducibility"), by recursion on the type:

* `R bool t`: `t` reduces to `true` or to `false`;
* `R (A ⇒ B) t`: `t` halts, and applied to any `R A` argument it gives an `R B` result. -/
def R : Ty → Term → Prop
  | .bool, t => Star Step t .tru ∨ Star Step t .fls
  | .arrow A B, t => Halts t ∧ ∀ s, R A s → R B (.app t s)

theorem R_halts {T : Ty} {t : Term} : R T t → Halts t := by
  intro h
  cases T with
  | bool =>
    rcases h with h | h
    · exact ⟨_, h, .tru⟩
    · exact ⟨_, h, .fls⟩
  | arrow A B => exact h.1

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
  intro hs h
  induction T generalizing t t' with
  | bool =>
    rcases h with h | h
    · exact Or.inl (star_step_det h .tru hs)
    · exact Or.inr (star_step_det h .fls hs)
  | arrow A B _ ihB =>
    exact ⟨halts_fwd hs h.1, fun s hRs => ihB (.app1 hs) (h.2 s hRs)⟩

theorem R_star_back {T : Ty} {t t' : Term} : Star Step t t' → R T t' → R T t := by
  intro hs h
  induction hs with
  | refl => exact h
  | step h1 _ ih => exact R_back h1 (ih h)

theorem R_star_fwd {T : Ty} {t t' : Term} : Star Step t t' → R T t → R T t' := by
  intro hs h
  induction hs with
  | refl => exact h
  | step h1 _ ih => exact ih (R_fwd h1 h)

theorem rename_rename {ρ ρ' ρ'' : Nat → Nat} {t : Term} (h : ∀ x, ρ (ρ' x) = ρ'' x) :
    rename ρ (rename ρ' t) = rename ρ'' t := by
  induction t generalizing ρ ρ' ρ'' with
  | var x => simp [rename, h]
  | lam A t ih =>
    simp only [rename]
    rw [ih]
    -- left: the lifted renamings still compose
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [ext, h]
  | app f a ihf iha => simp [rename, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, ihc h, iht h, ihe h]

theorem subst_rename {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}
    (h : ∀ x, σ (ρ x) = τ x) :
    subst σ (rename ρ t) = subst τ t := by
  induction t generalizing σ τ ρ with
  | var x => simp [rename, subst, h]
  | lam A t ih =>
    simp only [rename, subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [ext, exts, h]
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]

theorem rename_subst {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}
    (h : ∀ x, rename ρ (σ x) = τ x) :
    rename ρ (subst σ t) = subst τ t := by
  induction t generalizing σ τ ρ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [rename, subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n =>
      -- goal: rename (ext ρ) (exts σ (n + 1)) = exts τ (n + 1)
      simp only [exts, ← h n]
      have e1 : rename (ext ρ) (rename Nat.succ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
        rename_rename (fun _ => rfl)
      have e2 : rename Nat.succ (rename ρ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
        rename_rename (fun _ => rfl)
      rw [e1, e2]
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]

theorem subst_subst {σ τ υ : Nat → Term} {t : Term} (h : ∀ x, subst τ (σ x) = υ x) :
    subst τ (subst σ t) = subst υ t := by
  induction t generalizing σ τ υ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n =>
      -- goal: subst (exts τ) (exts σ (n + 1)) = exts υ (n + 1)
      simp only [exts, ← h n]
      have e1 : subst (exts τ) (rename Nat.succ (σ n)) = subst (fun x => rename Nat.succ (τ x)) (σ n) :=
        subst_rename (fun _ => rfl)
      have e2 : rename Nat.succ (subst τ (σ n)) = subst (fun x => rename Nat.succ (τ x)) (σ n) :=
        rename_subst (fun _ => rfl)
      rw [e1, e2]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [subst, ihc h, iht h, ihe h]

theorem subst_id {σ : Nat → Term} {t : Term} (h : ∀ x, σ x = .var x) : subst σ t = t := by
  induction t generalizing σ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [exts, h, rename]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [subst, ihc h, iht h, ihe h]

/-- `scons v σ` maps `0` to `v` and `n + 1` to `σ n`
(written `v · σ` on paper). -/
def scons (v : Term) (σ : Nat → Term) : Nat → Term
  | 0 => v
  | n + 1 => σ n

theorem subst1_exts {v : Term} {σ : Nat → Term} {t : Term} :
    subst (subst1 v) (subst (exts σ) t) = subst (scons v σ) t := by
  apply subst_subst
  intro x
  cases x with
  | zero => rfl
  | succ n =>
    show subst (subst1 v) (rename Nat.succ (σ n)) = σ n
    have e : subst (subst1 v) (rename Nat.succ (σ n)) = subst Term.var (σ n) :=
      subst_rename (fun _ => rfl)
    rw [e, subst_id (fun _ => rfl)]

/-! ## The fundamental lemma -/

/-- `σ` is an *instantiation* of `Γ`: it maps each variable of `Γ` to a
reducible term of the right type. -/
def Inst (Γ : Ctx) (σ : Nat → Term) : Prop := ∀ x A, Γ[x]? = some A → R A (σ x)

theorem inst_cons {Γ : Ctx} {σ : Nat → Term} {A : Ty} {v : Term} :
    Inst Γ σ → R A v → Inst (A :: Γ) (scons v σ) := by
  intro hσ hv x B hx
  cases x with
  | zero =>
    simp at hx
    rw [← hx]
    exact hv
  | succ n => exact hσ n B hx

theorem fundamental {Γ : Ctx} {t : Term} {T : Ty} {σ : Nat → Term} :
    HasType Γ t T → Inst Γ σ → R T (subst σ t) := by
  intro ht hσ
  induction ht generalizing σ with
  | var h => exact hσ _ _ h
  | @lam Γ A t B _ ih =>
    -- goal: R (A ⇒ B) (subst σ (.lam A t)), which is by definition
    --       R (A ⇒ B) (.lam A (subst (exts σ) t))
    refine ⟨value_halts .lam, fun s hs => ?_⟩
    obtain ⟨v, hsv, hv⟩ := R_halts hs
    have hRv : R A v := R_star_fwd hsv hs
    have hbody : R B (subst (scons v σ) t) := ih (inst_cons hσ hRv)
    rw [← subst1_exts] at hbody
    apply R_star_back (star_app2 .lam hsv)
    exact R_back (.beta hv) hbody
  | app _ _ ihf iha => exact (ihf hσ).2 _ (iha hσ)
  | tru => exact Or.inl (.refl _)
  | fls => exact Or.inr (.refl _)
  | ite _ _ _ ihc iht ihe =>
    rcases ihc hσ with hc | hc
    · exact R_star_back (star_trans (star_ite hc) (.step .iteTrue (.refl _))) (iht hσ)
    · exact R_star_back (star_trans (star_ite hc) (.step .iteFalse (.refl _))) (ihe hσ)
