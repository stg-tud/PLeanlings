/-
# 17.03 — Extending STLC: sums

Products are "A *and* B"; sums are "A *or* B", the tagged unions of
functional languages (`Either A B` in Haskell, `Sum A B` in Lean, `enum`
in Rust). A value of type `sum A B` is either `inl a` with `a : A` or `inr b`
with `b : B`, and `case` inspects the tag:

    case t of inl x => l | inr y => r

Both branches bind a variable: `x : A` in `l` and `y : B` in `r`. With de
Bruijn indices, the branches are simply terms with one extra free variable
(`var 0`), just like the body of a `lam`. So `case t l r` binds `var 0` in `l`
and in `r`.

**Annotations.** In `inl a`, the type of `a` determines `A`, but nothing
determines `B`. Without annotations, `inl tru` would have type `sum bool B`
for *every* `B`, and types would no longer be unique. Following TAPL, we
annotate the *other* type: `inl B a : sum A B` and `inr A b : sum A B`.

     Γ ⊢ a : A                       Γ ⊢ b : B
    ──────────────────────── inl   ──────────────────────── inr
     Γ ⊢ inl B a : sum A B          Γ ⊢ inr A b : sum A B

     Γ ⊢ t : sum A B    A :: Γ ⊢ l : C    B :: Γ ⊢ r : C
    ───────────────────────────────────────────────────── case
                  Γ ⊢ case t l r : C

Values are `inl B v` and `inr A v` for values `v`. Reduction:

         Value v                                   Value v
    ───────────────────────────────── caseInl  ───────────────────────────────── caseInr
     case (inl B v) l r ⟶ l[v]                case (inr A v) l r ⟶ r[v]

         t ⟶ t'                    t ⟶ t'                        t ⟶ t'
    ─────────────────────── inl  ─────────────────────── inr  ─────────────────────────────── case
     inl B t ⟶ inl B t'          inr A t ⟶ inr A t'          case t l r ⟶ case t' l r

## Your task

1. Fill in the `case` cases of `rename` and `subst`. Careful with the binders.
2. Prove `canonical_sum`.
3. Fill in the `case` cases of `progress`, `rename_typing`, `subst_typing` and
   `preservation`.
4. Fill in the `inl` and `case` cases of `type_unique`. The `inl` case is
   where the annotation is needed.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types: `T ::= bool | T ⇒ T | sum T T`. -/
inductive Ty where
  | bool
  | arrow (A B : Ty)
  | sum (A B : Ty)
  deriving DecidableEq, Repr

/-- `A ⇒ B` is the function type. It associates to the right. -/
infixr:70 " ⇒ " => Ty.arrow

/-- Terms with de Bruijn indices. `lam A t` binds variable `0` (of type `A`) in `t`.
`case t l r` binds variable `0` in `l` and in `r`. -/
inductive Term where
  | var (x : Nat)
  | lam (A : Ty) (body : Term)
  | app (f a : Term)
  | tru
  | fls
  | ite (c t e : Term)
  | inl (B : Ty) (t : Term)
  | inr (A : Ty) (t : Term)
  | case (t l r : Term)
  deriving DecidableEq, Repr

/-- A context lists the types of the free variables: `Γ[0]?` is the type of `var 0`. -/
abbrev Ctx := List Ty

/-- `HasType Γ t T` means `Γ ⊢ t : T`. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (.var x) A
  | lam {Γ A t B} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ c t e A} : HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A
  | inl {Γ t A B} : HasType Γ t A → HasType Γ (.inl B t) (.sum A B)
  | inr {Γ t A B} : HasType Γ t B → HasType Γ (.inr A t) (.sum A B)
  | case {Γ t l r A B C} : HasType Γ t (.sum A B) → HasType (A :: Γ) l C → HasType (B :: Γ) r C →
      HasType Γ (.case t l r) C

/-- Lift a renaming under a binder: `0` stays `0`, `n + 1` becomes `ρ n + 1`. -/
def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-! ## Renaming and substitution -/

/-- Apply the renaming `ρ` to all free variables. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .var x => .var (ρ x)
  | .lam A t => .lam A (rename (ext ρ) t)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)
  | .inl B t => .inl B (rename ρ t)
  | .inr A t => .inr A (rename ρ t)
  | .case t l r => sorry

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
  | .inl B t => .inl B (subst σ t)
  | .inr A t => .inr A (subst σ t)
  | .case t l r => sorry

/-! ## Values, reduction and metatheory

The new definitions are given; the holes are the new proof cases. -/

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions, booleans, and injections of values. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls
  | inl {B v} : Value v → Value (.inl B v)
  | inr {A v} : Value v → Value (.inr A v)

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | inl {B t t'} : Step t t' → Step (.inl B t) (.inl B t')
  | inr {A t t'} : Step t t' → Step (.inr A t) (.inr A t')
  | caseInl {B v l r} : Value v → Step (.case (.inl B v) l r) (subst (subst1 v) l)
  | caseInr {A v l r} : Value v → Step (.case (.inr A v) l r) (subst (subst1 v) r)
  | case {t t' l r} : Step t t' → Step (.case t l r) (.case t' l r)

theorem canonical_bool {Γ : Ctx} {v : Term} :
    HasType Γ v .bool → Value v → v = .tru ∨ v = .fls := by
  intro ht hv
  cases hv with
  | tru => exact Or.inl rfl
  | fls => exact Or.inr rfl
  | _ => cases ht

theorem canonical_arrow {Γ : Ctx} {v : Term} {A B : Ty} :
    HasType Γ v (A ⇒ B) → Value v → ∃ t, v = .lam A t := by
  intro ht hv
  cases hv with
  | lam =>
    cases ht
    exact ⟨_, rfl⟩
  | _ => cases ht

theorem ext_ok {Γ Δ : Ctx} {ρ : Nat → Nat} {B : Ty}
    (hρ : ∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) :
    ∀ x A, (B :: Γ)[x]? = some A → (B :: Δ)[ext ρ x]? = some A := by
  intro x A hx
  cases x with
  | zero => exact hx
  | succ n => exact hρ n A hx

theorem rename_typing {Γ Δ : Ctx} {ρ : Nat → Nat} {t : Term} {T : Ty}
    (hρ : ∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) :
    HasType Γ t T → HasType Δ (rename ρ t) T := by
  intro ht
  induction ht generalizing Δ ρ with
  | var h => exact .var (hρ _ _ h)
  | lam _ ih => exact .lam (ih (ext_ok hρ))
  | app _ _ ihf iha => exact .app (ihf hρ) (iha hρ)
  | tru => exact .tru
  | fls => exact .fls
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hρ) (iht hρ) (ihe hρ)
  | inl _ ih => exact .inl (ih hρ)
  | inr _ ih => exact .inr (ih hρ)
  | case _ _ _ iht ihl ihr => sorry

theorem weakening {Γ : Ctx} {t : Term} {T B : Ty} :
    HasType Γ t T → HasType (B :: Γ) (rename Nat.succ t) T :=
  rename_typing (fun _ _ h => h)

theorem exts_ok {Γ Δ : Ctx} {σ : Nat → Term} {B : Ty}
    (hσ : ∀ x A, Γ[x]? = some A → HasType Δ (σ x) A) :
    ∀ x A, (B :: Γ)[x]? = some A → HasType (B :: Δ) (exts σ x) A := by
  intro x A hx
  cases x with
  | zero => exact .var hx
  | succ n => exact weakening (hσ n A hx)

theorem subst1_ok {Γ : Ctx} {s : Term} {A : Ty} (hs : HasType Γ s A) :
    ∀ x B, (A :: Γ)[x]? = some B → HasType Γ (subst1 s x) B := by
  intro x B hx
  cases x with
  | zero =>
    simp at hx
    rw [← hx]
    exact hs
  | succ n => exact .var hx

/-! ## Sums: canonical forms, progress, preservation, uniqueness -/

theorem canonical_sum {Γ : Ctx} {v : Term} {A B : Ty} :
    HasType Γ v (.sum A B) → Value v →
      (∃ w, v = .inl B w ∧ Value w) ∨ (∃ w, v = .inr A w ∧ Value w) := by
  sorry

theorem progress {t : Term} {T : Ty} :
    HasType [] t T → Value t ∨ ∃ t', Step t t' := by
  intro ht
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var h =>
    subst hΓ
    cases h
  | lam _ _ => exact Or.inl .lam
  | app hf ha ihf iha =>
    subst hΓ
    rcases ihf rfl with hvf | ⟨f', hf'⟩
    · rcases iha rfl with hva | ⟨a', ha'⟩
      · obtain ⟨t, rfl⟩ := canonical_arrow hf hvf
        exact Or.inr ⟨_, .beta hva⟩
      · exact Or.inr ⟨_, .app2 hvf ha'⟩
    · exact Or.inr ⟨_, .app1 hf'⟩
  | tru => exact Or.inl .tru
  | fls => exact Or.inl .fls
  | ite hc _ _ ihc _ _ =>
    subst hΓ
    rcases ihc rfl with hvc | ⟨c', hc'⟩
    · rcases canonical_bool hc hvc with rfl | rfl
      · exact Or.inr ⟨_, .iteTrue⟩
      · exact Or.inr ⟨_, .iteFalse⟩
    · exact Or.inr ⟨_, .ite hc'⟩
  | inl _ ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · exact Or.inl (.inl hv)
    · exact Or.inr ⟨_, .inl ht'⟩
  | inr _ ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · exact Or.inl (.inr hv)
    · exact Or.inr ⟨_, .inr ht'⟩
  | case h _ _ iht _ _ =>
    subst hΓ
    sorry

theorem subst_typing {Γ Δ : Ctx} {σ : Nat → Term} {t : Term} {T : Ty}
    (hσ : ∀ x A, Γ[x]? = some A → HasType Δ (σ x) A) :
    HasType Γ t T → HasType Δ (subst σ t) T := by
  intro ht
  induction ht generalizing Δ σ with
  | var h => exact hσ _ _ h
  | lam _ ih => exact .lam (ih (exts_ok hσ))
  | app _ _ ihf iha => exact .app (ihf hσ) (iha hσ)
  | tru => exact .tru
  | fls => exact .fls
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hσ) (iht hσ) (ihe hσ)
  | inl _ ih => exact .inl (ih hσ)
  | inr _ ih => exact .inr (ih hσ)
  | case _ _ _ iht ihl ihr => sorry

theorem subst1_typing {Γ : Ctx} {s t : Term} {A B : Ty} :
    HasType (A :: Γ) t B → HasType Γ s A → HasType Γ (subst (subst1 s) t) B :=
  fun ht hs => subst_typing (subst1_ok hs) ht

theorem preservation {Γ : Ctx} {t t' : Term} {T : Ty} :
    HasType Γ t T → Step t t' → HasType Γ t' T := by
  intro ht hs
  induction ht generalizing t' with
  | var _ => cases hs
  | lam _ _ => cases hs
  | app hf ha ihf iha =>
    cases hs with
    | beta _ =>
      cases hf with
      | lam hbody => exact subst1_typing hbody ha
    | app1 hs' => exact .app (ihf hs') ha
    | app2 _ hs' => exact .app hf (iha hs')
  | tru => cases hs
  | fls => cases hs
  | ite hc ht he ihc _ _ =>
    cases hs with
    | iteTrue => exact ht
    | iteFalse => exact he
    | ite hs' => exact .ite (ihc hs') ht he
  | inl _ ih =>
    cases hs with
    | inl hs' => exact .inl (ih hs')
  | inr _ ih =>
    cases hs with
    | inr hs' => exact .inr (ih hs')
  | case ht hl hr iht _ _ =>
    sorry

theorem preservation_star {Γ : Ctx} {t t' : Term} {T : Ty} :
    HasType Γ t T → Star Step t t' → HasType Γ t' T := by
  intro ht hs
  induction hs with
  | refl => exact ht
  | step h₁ _ ih => exact ih (preservation ht h₁)

theorem type_safety {t t' : Term} {T : Ty} :
    HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := by
  intro ht hs
  exact progress (preservation_star ht hs)

theorem type_unique {Γ : Ctx} {t : Term} {A B : Ty} :
    HasType Γ t A → HasType Γ t B → A = B := by
  intro h1 h2
  induction h1 generalizing B with
  | var h =>
    cases h2 with
    | var h' =>
      rw [h] at h'
      injection h'
  | lam _ ih =>
    cases h2 with
    | lam h' => rw [ih h']
  | app _ _ ihf _ =>
    cases h2 with
    | app hf' _ =>
      have h := ihf hf'
      injection h
  | tru => cases h2; rfl
  | fls => cases h2; rfl
  | ite _ _ _ _ iht _ =>
    cases h2 with
    | ite _ ht' _ => exact iht ht'
  | inl _ ih =>
    sorry
  | inr _ ih =>
    cases h2 with
    | inr h' => rw [ih h']
  | case _ _ _ iht ihl _ =>
    sorry
