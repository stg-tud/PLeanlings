/- HINT
The constructors are direct translations of the rules, in the style of the
others, for example
`| letIn {Γ t body A B} : HasType Γ t A → HasType (A :: Γ) body B → HasType Γ (.letIn t body) B`.
For the steps, compare with `beta` and `app2`. In `rename` and `subst`, `body` sits
under a binder, so it needs `ext ρ` resp. `exts σ`, just like the body of a `lam`.

The proof cases follow the `app` cases:
* `progress`: `| letIn _ _ iht _ => subst hΓ; rcases iht rfl with hv | ⟨t', ht'⟩ …`.
  Both alternatives step.
* `rename_typing`/`subst_typing`: `.letIn (iht hρ) (ihb (ext_ok hρ))`.
* `preservation`: `cases hs`; the `letBeta` case is `subst1_typing hb ht`.
-/

-- The theorems must have their original statements.
example : ∀ {t : Term} {T : Ty}, HasType [] t T → Value t ∨ ∃ t', Step t t' := @progress
example : ∀ {Γ Δ : Ctx} {ρ : Nat → Nat} {t : Term} {T : Ty}, (∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) → HasType Γ t T → HasType Δ (rename ρ t) T := @rename_typing
example : ∀ {Γ Δ : Ctx} {σ : Nat → Term} {t : Term} {T : Ty}, (∀ x A, Γ[x]? = some A → HasType Δ (σ x) A) → HasType Γ t T → HasType Δ (subst σ t) T := @subst_typing
example : ∀ {Γ : Ctx} {t t' : Term} {T : Ty}, HasType Γ t T → Step t t' → HasType Γ t' T := @preservation
example : ∀ {t t' : Term} {T : Ty}, HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := @type_safety
-- The new rules.
example {Γ : Ctx} {t body : Term} {A B : Ty} (h₁ : HasType Γ t A) (h₂ : HasType (A :: Γ) body B) :
    HasType Γ (.letIn t body) B := .letIn h₁ h₂
example {v body : Term} (h : Value v) : Step (.letIn v body) (subst (subst1 v) body) := .letBeta h
example {t t' body : Term} (h : Step t t') : Step (.letIn t body) (.letIn t' body) := .let1 h
example : ¬ HasType [] (.letIn .tru (.succ (.var 0))) .nat := by
  intro h
  cases h with
  | letIn h₁ h₂ =>
    cases h₁ with
    | tru =>
      cases h₂ with
      | succ h => cases h with | var h => cases h
example : ¬ HasType [] (.letIn .zero (.var 1)) .nat := by
  intro h
  cases h with
  | letIn _ h₂ => cases h₂ with | var h => cases h
example : ∀ t, ¬ Step (.letIn (.var 0) .tru) t := by
  intro t h
  cases h with
  | letBeta h => cases h
  | let1 h => cases h
example : ¬ Value (.letIn .tru .tru) := by intro h; cases h
-- The old typing rules must be unchanged.
example : ∀ {Γ : Ctx} {x : Nat} {A : Ty}, Γ[x]? = some A → HasType Γ (.var x) A := @HasType.var
example : ∀ {Γ : Ctx} {A : Ty} {t : Term} {B : Ty}, HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B) := @HasType.lam
example : ∀ {Γ : Ctx} {f a : Term} {A B : Ty}, HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B := @HasType.app
example : ∀ {Γ : Ctx}, HasType Γ .tru .bool := @HasType.tru
example : ∀ {Γ : Ctx}, HasType Γ .fls .bool := @HasType.fls
example : ∀ {Γ : Ctx} {c t e : Term} {A : Ty}, HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A := @HasType.ite
example : ∀ {Γ : Ctx}, HasType Γ .zero .nat := @HasType.zero
example : ∀ {Γ : Ctx} {t : Term}, HasType Γ t .nat → HasType Γ (.succ t) .nat := @HasType.succ
example : ∀ {Γ : Ctx} {t : Term}, HasType Γ t .nat → HasType Γ (.pred t) .nat := @HasType.pred
example : ∀ {Γ : Ctx} {t : Term}, HasType Γ t .nat → HasType Γ (.iszero t) .bool := @HasType.iszero
example : ¬ HasType [] (.app .tru .zero) .nat := by
  intro h
  cases h with
  | app h _ => cases h
example : ¬ HasType [] (.var 0) .nat := by
  intro h
  cases h with
  | var h => cases h
example : ¬ HasType [] (.succ .tru) .nat := by
  intro h
  cases h with
  | succ h => cases h
-- The values must be the original ones.
example : ∀ {A : Ty} {t : Term}, Value (.lam A t) := @Value.lam
example : Value .tru := Value.tru
example : Value .fls := Value.fls
example : Value .zero := Value.zero
example : ∀ {v : Term}, Value v → Value (.succ v) := @Value.succ
example : ¬ Value (.var 0) := by intro h; cases h
example : ¬ Value (.app .tru .tru) := by intro h; cases h
example : ¬ Value (.pred .zero) := by intro h; cases h
-- The old reduction rules must be unchanged.
example : ∀ {A : Ty} {t v : Term}, Value v → Step (.app (.lam A t) v) (subst (subst1 v) t) := @Step.beta
example : ∀ {f f' a : Term}, Step f f' → Step (.app f a) (.app f' a) := @Step.app1
example : ∀ {v a a' : Term}, Value v → Step a a' → Step (.app v a) (.app v a') := @Step.app2
example : ∀ {t e : Term}, Step (.ite .tru t e) t := @Step.iteTrue
example : ∀ {t e : Term}, Step (.ite .fls t e) e := @Step.iteFalse
example : ∀ {c c' t e : Term}, Step c c' → Step (.ite c t e) (.ite c' t e) := @Step.ite
example : ∀ {t t' : Term}, Step t t' → Step (.succ t) (.succ t') := @Step.succ
example : Step (.pred .zero) .zero := Step.predZero
example : ∀ {v : Term}, Value v → Step (.pred (.succ v)) v := @Step.predSucc
example : ∀ {t t' : Term}, Step t t' → Step (.pred t) (.pred t') := @Step.pred
example : Step (.iszero .zero) .tru := Step.iszeroZero
example : ∀ {v : Term}, Value v → Step (.iszero (.succ v)) .fls := @Step.iszeroSucc
example : ∀ {t t' : Term}, Step t t' → Step (.iszero t) (.iszero t') := @Step.iszero
example : ∀ t, ¬ Step .tru t := by intro t h; cases h
example : ∀ t, ¬ Step (.lam .nat (.pred .zero)) t := by intro t h; cases h
example : ∀ t, ¬ Step (.app .tru .zero) t := by
  intro t h
  cases h with
  | app1 h => cases h
  | app2 _ h => cases h
-- Renaming and substitution, including the new cases.
example : ext (· + 3) 0 = 0 := rfl
example : ext (· + 3) 2 = 5 := rfl
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename Nat.succ (.ite (.var 0) (.succ (.var 1)) (.iszero (.pred .zero))) = .ite (.var 1) (.succ (.var 2)) (.iszero (.pred .zero)) := rfl
example : rename (· + 5) (.letIn (.var 0) (.app (.var 0) (.var 1))) = .letIn (.var 5) (.app (.var 0) (.var 6)) := rfl
example : exts (fun n => .var (n + 7)) 0 = .var 0 := rfl
example : exts (fun n => .var (n + 7)) 2 = .var 9 := rfl
example : subst (subst1 .tru) (.lam .nat (.app (.var 1) (.var 0))) = .lam .nat (.app .tru (.var 0)) := rfl
example : subst (subst1 (.var 0)) (.lam .nat (.var 1)) = .lam .nat (.var 1) := rfl
example : subst (subst1 .zero) (.ite (.var 0) (.succ (.var 1)) (.iszero (.pred .fls))) = .ite .zero (.succ (.var 0)) (.iszero (.pred .fls)) := rfl
example : subst (subst1 .zero) (.letIn (.var 0) (.app (.var 0) (.var 1))) = .letIn .zero (.app (.var 0) .zero) := rfl
example : subst (subst1 (.var 0)) (.letIn (.var 1) (.letIn (.var 0) (.var 2))) = .letIn (.var 0) (.letIn (.var 0) (.var 2)) := rfl
-- `let x = 0 in succ x` evaluates to `1` in two steps.
example : Star Step (.letIn .zero (.succ (.var 0))) (.succ .zero) :=
  .step (.letBeta .zero) (.refl _)
example : Star Step (.letIn (.pred (.succ .zero)) (.succ (.var 0))) (.succ .zero) :=
  .step (.let1 (.predSucc .zero)) (.step (.letBeta .zero) (.refl _))
