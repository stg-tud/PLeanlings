/-
# 17.02 — Extending STLC: products

Next, pairs. A new type former `prod A B` (written `A × B` on paper) comes with
an introduction form and two elimination forms:

    pair a b        -- the pair (a, b)
    fst t           -- first component
    snd t           -- second component

The typing rules:

     Γ ⊢ a : A    Γ ⊢ b : B              Γ ⊢ t : prod A B          Γ ⊢ t : prod A B
    ───────────────────────── pair      ─────────────────── fst    ─────────────────── snd
     Γ ⊢ pair a b : prod A B              Γ ⊢ fst t : A              Γ ⊢ snd t : B

A pair is a value when both components are values. Evaluation is again
call-by-value and left-to-right: first the left component, then the right one,
and projections only fire on fully evaluated pairs:

        a ⟶ a'                         Value v    b ⟶ b'
    ──────────────────────── pair1   ──────────────────────── pair2
     pair a b ⟶ pair a' b             pair v b ⟶ pair v b'

     Value v   Value w                    Value v   Value w
    ──────────────────────── fstPair    ──────────────────────── sndPair
     fst (pair v w) ⟶ v                  snd (pair v w) ⟶ w

        t ⟶ t'                            t ⟶ t'
    ──────────────────── fst            ──────────────────── snd
     fst t ⟶ fst t'                      snd t ⟶ snd t'

To keep the file short, this language has no natural numbers, only `bool`,
functions and products.

The new value form needs a new **canonical forms** lemma: a value of a product
type is a pair of values. Progress uses it for the projections, in the same way
it uses `canonical_arrow` for `app`.

## Your task

1. Prove `canonical_prod`.
2. Fill in the `pair`, `fst` and `snd` cases of `progress` and `preservation`.
3. Write `swap A B : Term`, the function `λp : prod A B. (snd p, fst p)`, and
   prove that it has type `prod A B ⇒ prod B A` for all `A`, `B`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types: `T ::= bool | T ⇒ T | prod T T`. -/
inductive Ty where
  | bool
  | arrow (A B : Ty)
  | prod (A B : Ty)
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
  | pair (a b : Term)
  | fst (t : Term)
  | snd (t : Term)
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
  | pair {Γ a b A B} : HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (.prod A B)
  | fst {Γ t A B} : HasType Γ t (.prod A B) → HasType Γ (.fst t) A
  | snd {Γ t A B} : HasType Γ t (.prod A B) → HasType Γ (.snd t) B

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
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst t => .fst (rename ρ t)
  | .snd t => .snd (rename ρ t)

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
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst t => .fst (subst σ t)
  | .snd t => .snd (subst σ t)

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions, booleans and pairs of values. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls
  | pair {v w} : Value v → Value w → Value (.pair v w)

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | pair1 {a a' b} : Step a a' → Step (.pair a b) (.pair a' b)
  | pair2 {v b b'} : Value v → Step b b' → Step (.pair v b) (.pair v b')
  | fstPair {v w} : Value v → Value w → Step (.fst (.pair v w)) v
  | sndPair {v w} : Value v → Value w → Step (.snd (.pair v w)) w
  | fst {t t'} : Step t t' → Step (.fst t) (.fst t')
  | snd {t t'} : Step t t' → Step (.snd t) (.snd t')

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
  | pair _ _ iha ihb => exact .pair (iha hρ) (ihb hρ)
  | fst _ ih => exact .fst (ih hρ)
  | snd _ ih => exact .snd (ih hρ)

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
  | pair _ _ iha ihb => exact .pair (iha hσ) (ihb hσ)
  | fst _ ih => exact .fst (ih hσ)
  | snd _ ih => exact .snd (ih hσ)

theorem subst1_ok {Γ : Ctx} {s : Term} {A : Ty} (hs : HasType Γ s A) :
    ∀ x B, (A :: Γ)[x]? = some B → HasType Γ (subst1 s x) B := by
  intro x B hx
  cases x with
  | zero =>
    simp at hx
    rw [← hx]
    exact hs
  | succ n => exact .var hx

theorem subst1_typing {Γ : Ctx} {s t : Term} {A B : Ty} :
    HasType (A :: Γ) t B → HasType Γ s A → HasType Γ (subst (subst1 s) t) B :=
  fun ht hs => subst_typing (subst1_ok hs) ht

/-! ## Products: canonical forms, progress and preservation -/

theorem canonical_prod {Γ : Ctx} {v : Term} {A B : Ty} :
    HasType Γ v (.prod A B) → Value v → ∃ a b, v = .pair a b ∧ Value a ∧ Value b := by
  intro ht hv
  cases hv with
  | pair ha hb => exact ⟨_, _, rfl, ha, hb⟩
  | _ => cases ht

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
  | pair _ _ iha ihb =>
    subst hΓ
    rcases iha rfl with hva | ⟨a', ha'⟩
    · rcases ihb rfl with hvb | ⟨b', hb'⟩
      · exact Or.inl (.pair hva hvb)
      · exact Or.inr ⟨_, .pair2 hva hb'⟩
    · exact Or.inr ⟨_, .pair1 ha'⟩
  | fst h ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · obtain ⟨a, b, rfl, ha, hb⟩ := canonical_prod h hv
      exact Or.inr ⟨_, .fstPair ha hb⟩
    · exact Or.inr ⟨_, .fst ht'⟩
  | snd h ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · obtain ⟨a, b, rfl, ha, hb⟩ := canonical_prod h hv
      exact Or.inr ⟨_, .sndPair ha hb⟩
    · exact Or.inr ⟨_, .snd ht'⟩

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
  | pair ha hb iha ihb =>
    cases hs with
    | pair1 hs' => exact .pair (iha hs') hb
    | pair2 _ hs' => exact .pair ha (ihb hs')
  | fst h ih =>
    cases hs with
    | fstPair _ _ =>
      cases h with
      | pair ha _ => exact ha
    | fst hs' => exact .fst (ih hs')
  | snd h ih =>
    cases hs with
    | sndPair _ _ =>
      cases h with
      | pair _ hb => exact hb
    | snd hs' => exact .snd (ih hs')

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

/-! ## A program -/

/-- `λp : prod A B. (snd p, fst p)` -/
def swap (A B : Ty) : Term := .lam (.prod A B) (.pair (.snd (.var 0)) (.fst (.var 0)))

theorem swap_typed (A B : Ty) : HasType [] (swap A B) (.prod A B ⇒ .prod B A) :=
  .lam (.pair (.snd (.var rfl)) (.fst (.var rfl)))
