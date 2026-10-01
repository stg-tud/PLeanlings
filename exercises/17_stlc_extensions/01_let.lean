/-
# 17.01 — Extending STLC: `let`

Welcome to the bonus chapters! In this chapter, you extend the STLC of chapters
14–16 with new language features. Every file contains the complete development
(syntax, typing, substitution, reduction and the type-safety proof), and every
new construct means new cases in the definitions and proofs. This is what
"extending a language" looks like in a proof assistant: Lean tells you exactly
which cases are missing.

We start with the simplest extension, local definitions:

    let x = t in body

In de Bruijn notation, `x` is variable `0` of `body`, so the term is just
`letIn t body`, and `body` lives under one extra binder, just like the body of
a `lam`. The rules:

     Γ ⊢ t : A     A :: Γ ⊢ body : B
    ────────────────────────────────── letIn
         Γ ⊢ letIn t body : B

           Value v                                       t ⟶ t'
    ──────────────────────────────── letBeta   ──────────────────────────────── let1
     letIn v body ⟶ body[v]                    letIn t body ⟶ letIn t' body

where `body[v] = subst (subst1 v) body`. As for application, this is
call-by-value: `t` is evaluated to a value first, and only then substituted.

`let` is not really new: `letIn t body` behaves exactly like
`app (lam A body) t`, where `A` is the type of `t`. It types the same, and it
reduces the same (`let1` mirrors `app2` and `letBeta` mirrors `beta`).
Many languages treat `let` as syntactic sugar for exactly this.
The advantage of a separate `letIn` is that it needs no type annotation.

## Your task

The term `Term.letIn` is already there. Everything else is up to you:

1. Add the constructor `letIn` to `HasType` and the constructors `letBeta` and
   `let1` to `Step`, exactly as in the rules above (look for `TODO`).
2. Fill in the `letIn` cases of `rename` and `subst`. Remember that `body` is
   under a binder.
3. After step 1, Lean complains about missing cases in `progress`,
   `rename_typing`, `subst_typing` and `preservation`. Add them.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types: `T ::= bool | nat | T ⇒ T`. -/
inductive Ty where
  | bool
  | nat
  | arrow (A B : Ty)
  deriving DecidableEq, Repr

/-- `A ⇒ B` is the function type. It associates to the right. -/
infixr:70 " ⇒ " => Ty.arrow

/-- Terms with de Bruijn indices. `lam A t` binds variable `0` (of type `A`) in `t`,
and so does `letIn t body` in `body`. -/
inductive Term where
  | var (x : Nat)
  | lam (A : Ty) (body : Term)
  | app (f a : Term)
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  | letIn (t body : Term)
  deriving DecidableEq, Repr

/-- A context lists the types of the free variables: `Γ[0]?` is the type of `var 0`. -/
abbrev Ctx := List Ty

/-! ## The extended language -/

/-- `HasType Γ t T` means `Γ ⊢ t : T`. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (.var x) A
  | lam {Γ A t B} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ c t e A} : HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A
  | zero {Γ} : HasType Γ .zero .nat
  | succ {Γ t} : HasType Γ t .nat → HasType Γ (.succ t) .nat
  | pred {Γ t} : HasType Γ t .nat → HasType Γ (.pred t) .nat
  | iszero {Γ t} : HasType Γ t .nat → HasType Γ (.iszero t) .bool
  -- TODO: add the typing rule `letIn` here.

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
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .pred t => .pred (rename ρ t)
  | .iszero t => .iszero (rename ρ t)
  | .letIn t body => sorry

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
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .pred t => .pred (subst σ t)
  | .iszero t => .iszero (subst σ t)
  | .letIn t body => sorry

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions, booleans and numerals. (`letIn` is never a value.) -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls
  | zero : Value .zero
  | succ {v} : Value v → Value (.succ v)

/-- Call-by-value small-step reduction `t ⟶ t'` (rules as in chapter 14, plus `let`). -/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t'} : Step t t' → Step (.succ t) (.succ t')
  | predZero : Step (.pred .zero) .zero
  | predSucc {v} : Value v → Step (.pred (.succ v)) v
  | pred {t t'} : Step t t' → Step (.pred t) (.pred t')
  | iszeroZero : Step (.iszero .zero) .tru
  | iszeroSucc {v} : Value v → Step (.iszero (.succ v)) .fls
  | iszero {t t'} : Step t t' → Step (.iszero t) (.iszero t')
  -- TODO: add the reduction rules `letBeta` and `let1` here.

/-! ## Metatheory -/

theorem canonical_bool {Γ : Ctx} {v : Term} :
    HasType Γ v .bool → Value v → v = .tru ∨ v = .fls := by
  intro ht hv
  cases hv with
  | tru => exact Or.inl rfl
  | fls => exact Or.inr rfl
  | _ => cases ht

theorem canonical_nat {Γ : Ctx} {v : Term} :
    HasType Γ v .nat → Value v → v = .zero ∨ ∃ n, v = .succ n ∧ Value n := by
  intro ht hv
  cases hv with
  | zero => exact Or.inl rfl
  | succ hn => exact Or.inr ⟨_, rfl, hn⟩
  | _ => cases ht

theorem canonical_arrow {Γ : Ctx} {v : Term} {A B : Ty} :
    HasType Γ v (A ⇒ B) → Value v → ∃ t, v = .lam A t := by
  intro ht hv
  cases hv with
  | lam =>
    cases ht
    exact ⟨_, rfl⟩
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
  | zero => exact Or.inl .zero
  | succ _ ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · exact Or.inl (.succ hv)
    · exact Or.inr ⟨_, .succ ht'⟩
  | pred h ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · rcases canonical_nat h hv with rfl | ⟨n, rfl, hn⟩
      · exact Or.inr ⟨_, .predZero⟩
      · exact Or.inr ⟨_, .predSucc hn⟩
    · exact Or.inr ⟨_, .pred ht'⟩
  | iszero h ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · rcases canonical_nat h hv with rfl | ⟨n, rfl, hn⟩
      · exact Or.inr ⟨_, .iszeroZero⟩
      · exact Or.inr ⟨_, .iszeroSucc hn⟩
    · exact Or.inr ⟨_, .iszero ht'⟩

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
  | zero => exact .zero
  | succ _ ih => exact .succ (ih hρ)
  | pred _ ih => exact .pred (ih hρ)
  | iszero _ ih => exact .iszero (ih hρ)

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
  | zero => exact .zero
  | succ _ ih => exact .succ (ih hσ)
  | pred _ ih => exact .pred (ih hσ)
  | iszero _ ih => exact .iszero (ih hσ)

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
  | zero => cases hs
  | succ _ ih =>
    cases hs with
    | succ hs' => exact .succ (ih hs')
  | pred h ih =>
    cases hs with
    | predZero => exact .zero
    | predSucc _ =>
      cases h with
      | succ h' => exact h'
    | pred hs' => exact .pred (ih hs')
  | iszero _ ih =>
    cases hs with
    | iszeroZero => exact .tru
    | iszeroSucc _ => exact .fls
    | iszero hs' => exact .iszero (ih hs')

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
