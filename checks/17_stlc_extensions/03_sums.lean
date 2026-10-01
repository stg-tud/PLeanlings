/- HINT
`rename`/`subst`: the scrutinee `t` is not under a binder, but both branches are,
so they get `ext ρ` resp. `exts σ`.

`canonical_sum`: `cases hv`; in the `inl` and `inr` cases, `cases ht` makes Lean
match the annotation with `B` resp. `A`. Then e.g. `Or.inl ⟨_, rfl, hw⟩`.

`progress`: if the scrutinee is a value,
`rcases canonical_sum h hv with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩`.
`preservation`: `cases hs`; in `caseInl`, invert the typing of the scrutinee
(`cases ht with | inl hv => …`) and use `subst1_typing`.

`type_unique`, `case` case: the IH for `t` gives `sum A B = sum A' B'`.
`injection h with h₁ h₂` and `subst h₁` let you use the IH of the left branch.
-/

example : ∀ {Γ : Ctx} {v : Term} {A B : Ty}, HasType Γ v (.sum A B) → Value v → (∃ w, v = .inl B w ∧ Value w) ∨ (∃ w, v = .inr A w ∧ Value w) := @canonical_sum
example : ∀ {t : Term} {T : Ty}, HasType [] t T → Value t ∨ ∃ t', Step t t' := @progress
example : ∀ {Γ Δ : Ctx} {ρ : Nat → Nat} {t : Term} {T : Ty}, (∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) → HasType Γ t T → HasType Δ (rename ρ t) T := @rename_typing
example : ∀ {Γ Δ : Ctx} {σ : Nat → Term} {t : Term} {T : Ty}, (∀ x A, Γ[x]? = some A → HasType Δ (σ x) A) → HasType Γ t T → HasType Δ (subst σ t) T := @subst_typing
example : ∀ {Γ : Ctx} {t t' : Term} {T : Ty}, HasType Γ t T → Step t t' → HasType Γ t' T := @preservation
example : ∀ {t t' : Term} {T : Ty}, HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := @type_safety
example : ∀ {Γ : Ctx} {t : Term} {A B : Ty}, HasType Γ t A → HasType Γ t B → A = B := @type_unique
-- The typing rules must be the original ones.
example : ∀ {Γ : Ctx} {x : Nat} {A : Ty}, Γ[x]? = some A → HasType Γ (.var x) A := @HasType.var
example : ∀ {Γ : Ctx} {A : Ty} {t : Term} {B : Ty}, HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B) := @HasType.lam
example : ∀ {Γ : Ctx} {f a : Term} {A B : Ty}, HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B := @HasType.app
example : ∀ {Γ : Ctx}, HasType Γ .tru .bool := @HasType.tru
example : ∀ {Γ : Ctx}, HasType Γ .fls .bool := @HasType.fls
example : ∀ {Γ : Ctx} {c t e : Term} {A : Ty}, HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A := @HasType.ite
example : ∀ {Γ : Ctx} {t : Term} {A B : Ty}, HasType Γ t A → HasType Γ (.inl B t) (.sum A B) := @HasType.inl
example : ∀ {Γ : Ctx} {t : Term} {A B : Ty}, HasType Γ t B → HasType Γ (.inr A t) (.sum A B) := @HasType.inr
example : ∀ {Γ : Ctx} {t l r : Term} {A B C : Ty}, HasType Γ t (.sum A B) → HasType (A :: Γ) l C → HasType (B :: Γ) r C → HasType Γ (.case t l r) C := @HasType.case
example : ¬ HasType [] (.app .tru .fls) .bool := by
  intro h
  cases h with
  | app h _ => cases h
example : ¬ HasType [] (.var 0) .bool := by
  intro h
  cases h with
  | var h => cases h
example : ¬ HasType [] (.inl .bool .tru) (.sum .bool (.bool ⇒ .bool)) := by intro h; cases h
example : ¬ HasType [] (.case .tru .tru .tru) .bool := by
  intro h
  cases h with
  | case h _ _ => cases h
-- The values must be the original ones.
example : ∀ {A : Ty} {t : Term}, Value (.lam A t) := @Value.lam
example : Value .tru := Value.tru
example : Value .fls := Value.fls
example : ∀ {B : Ty} {v : Term}, Value v → Value (.inl B v) := @Value.inl
example : ∀ {A : Ty} {v : Term}, Value v → Value (.inr A v) := @Value.inr
example : ¬ Value (.var 0) := by intro h; cases h
example : ¬ Value (.app .tru .tru) := by intro h; cases h
example : ¬ Value (.case (.inl .bool .tru) .tru .tru) := by intro h; cases h
example : ¬ Value (.inl .bool (.var 0)) := by intro h; cases h with | inl h => cases h
example : ¬ Value (.inr .bool (.var 0)) := by intro h; cases h with | inr h => cases h
-- The reduction rules must be the original ones.
example : ∀ {A : Ty} {t v : Term}, Value v → Step (.app (.lam A t) v) (subst (subst1 v) t) := @Step.beta
example : ∀ {f f' a : Term}, Step f f' → Step (.app f a) (.app f' a) := @Step.app1
example : ∀ {v a a' : Term}, Value v → Step a a' → Step (.app v a) (.app v a') := @Step.app2
example : ∀ {t e : Term}, Step (.ite .tru t e) t := @Step.iteTrue
example : ∀ {t e : Term}, Step (.ite .fls t e) e := @Step.iteFalse
example : ∀ {c c' t e : Term}, Step c c' → Step (.ite c t e) (.ite c' t e) := @Step.ite
example : ∀ {B : Ty} {t t' : Term}, Step t t' → Step (.inl B t) (.inl B t') := @Step.inl
example : ∀ {A : Ty} {t t' : Term}, Step t t' → Step (.inr A t) (.inr A t') := @Step.inr
example : ∀ {B : Ty} {v l r : Term}, Value v → Step (.case (.inl B v) l r) (subst (subst1 v) l) := @Step.caseInl
example : ∀ {A : Ty} {v l r : Term}, Value v → Step (.case (.inr A v) l r) (subst (subst1 v) r) := @Step.caseInr
example : ∀ {t t' l r : Term}, Step t t' → Step (.case t l r) (.case t' l r) := @Step.case
example : ∀ t, ¬ Step .tru t := by intro t h; cases h
example : ∀ t, ¬ Step (.inl .bool .tru) t := by
  intro t h
  cases h with
  | inl h => cases h
example : ∀ t, ¬ Step (.case .tru .tru .tru) t := by
  intro t h
  cases h with
  | case h => cases h
example : ∀ t, ¬ Step (.case (.var 0) .tru .tru) t := by
  intro t h
  cases h with
  | case h => cases h
-- Renaming and substitution, including the new cases.
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename (· + 5) (.inl .bool (.inr .bool (.var 1))) = .inl .bool (.inr .bool (.var 6)) := rfl
example : rename (· + 5) (.case (.var 0) (.var 0) (.var 1)) = .case (.var 5) (.var 0) (.var 6) := rfl
example : rename (· + 5) (.case (.var 2) (.var 1) (.var 0)) = .case (.var 7) (.var 6) (.var 0) := rfl
example : subst (subst1 .tru) (.lam .bool (.app (.var 1) (.var 0))) = .lam .bool (.app .tru (.var 0)) := rfl
example : subst (subst1 .tru) (.inl .bool (.inr .bool (.var 0))) = .inl .bool (.inr .bool .tru) := rfl
example : subst (subst1 .tru) (.case (.var 0) (.var 0) (.var 1)) = .case .tru (.var 0) .tru := rfl
example : subst (subst1 (.var 0)) (.case (.var 1) (.var 1) (.var 2)) = .case (.var 0) (.var 1) (.var 1) := rfl
-- `case (inr bool fls) (inr bool x) (inl bool y)` swaps the tag in one step.
example : Step (.case (.inr .bool .fls) (.inr .bool (.var 0)) (.inl .bool (.var 0))) (.inl .bool .fls) :=
  .caseInr .fls
