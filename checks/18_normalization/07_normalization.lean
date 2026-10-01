/- HINT
`normalization`: `have h : R T (subst Term.var t) := fundamental ht (fun x A hx => by cases hx)`.
Then `rw [subst_id (fun _ => rfl)] at h` and `R_halts`.

`eval_of_star`: induction on the sequence. With `refl`, take `0` fuel; in the
`step h _ ih` case, use `n + 1` fuel and `simp [eval, step_complete h, hn]`.

`eval_terminates`: combine `normalization` and `eval_of_star`; `hn ▸ hv`
turns `hv : Value v` into `Value (eval n t)` given `hn : eval n t = v`.
-/

example : ∀ {t : Term} {T : Ty}, HasType [] t T → Halts t := @normalization
example : ∀ {t v : Term}, Star Step t v → Value v → ∃ n, eval n t = v := @eval_of_star
example : ∀ {t : Term} {T : Ty}, HasType [] t T → ∃ n, Value (eval n t) := @eval_terminates
example : ∀ {t t' : Term}, Step t t' → step t = some t' := @step_complete
example : ∀ {Γ : Ctx} {σ : Nat → Term} {A : Ty} {v : Term}, Inst Γ σ → R A v → Inst (A :: Γ) (scons v σ) := @inst_cons
example : ∀ {Γ : Ctx} {t : Term} {T : Ty} {σ : Nat → Term}, HasType Γ t T → Inst Γ σ → R T (subst σ t) := @fundamental
example : ∀ {σ τ υ : Nat → Term} {t : Term}, (∀ x, subst τ (σ x) = υ x) → subst τ (subst σ t) = subst υ t := @subst_subst
example : ∀ {σ : Nat → Term} {t : Term}, (∀ x, σ x = .var x) → subst σ t = t := @subst_id
example : ∀ {v : Term} {σ : Nat → Term} {t : Term}, subst (subst1 v) (subst (exts σ) t) = subst (scons v σ) t := @subst1_exts
example : ∀ {T : Ty} {t : Term}, R T t → Halts t := @R_halts
example : ∀ {T : Ty} {t t' : Term}, Step t t' → R T t' → R T t := @R_back
example : ∀ {T : Ty} {t t' : Term}, Step t t' → R T t → R T t' := @R_fwd
example : ∀ {T : Ty} {t t' : Term}, Star Step t t' → R T t' → R T t := @R_star_back
example : ∀ {T : Ty} {t t' : Term}, Star Step t t' → R T t → R T t' := @R_star_fwd
-- `Inst` must be the original definition.
example : ∀ Γ σ, Inst Γ σ = ∀ x A, Γ[x]? = some A → R A (σ x) := fun _ _ => rfl
-- `R` must be the original definition.
example : ∀ t, R .bool t = (Star Step t .tru ∨ Star Step t .fls) := fun _ => rfl
example : ∀ A B t, R (A ⇒ B) t = (Halts t ∧ ∀ s, R A s → R B (.app t s)) := fun _ _ _ => rfl
-- `Halts` must be the original definition.
example : ∀ t, Halts t = ∃ v, Star Step t v ∧ Value v := fun _ => rfl
example : ∀ {α : Type} {R : α → α → Prop} (a : α), Star R a a := @Star.refl
example : ∀ {α : Type} {R : α → α → Prop} {a b c : α}, R a b → Star R b c → Star R a c := @Star.step
-- The typing rules must be the original ones.
example : ∀ {Γ : Ctx} {x : Nat} {A : Ty}, Γ[x]? = some A → HasType Γ (.var x) A := @HasType.var
example : ∀ {Γ : Ctx} {A : Ty} {t : Term} {B : Ty}, HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B) := @HasType.lam
example : ∀ {Γ : Ctx} {f a : Term} {A B : Ty}, HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B := @HasType.app
example : ∀ {Γ : Ctx}, HasType Γ .tru .bool := @HasType.tru
example : ∀ {Γ : Ctx}, HasType Γ .fls .bool := @HasType.fls
example : ∀ {Γ : Ctx} {c t e : Term} {A : Ty}, HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A := @HasType.ite
example : ¬ HasType [] (.app .tru .fls) .bool := by
  intro h
  cases h with
  | app h _ => cases h
example : ¬ HasType [] (.var 0) .bool := by
  intro h
  cases h with
  | var h => cases h
example : ¬ HasType [] (.ite (.lam .bool (.var 0)) .tru .fls) .bool := by
  intro h
  cases h with
  | ite h _ _ => cases h
example : ¬ HasType [] (.lam .bool (.var 1)) (.bool ⇒ .bool) := by
  intro h
  cases h with
  | lam h =>
    cases h with
    | var h => cases h
-- The values must be the original ones.
example : ∀ {A : Ty} {t : Term}, Value (.lam A t) := @Value.lam
example : Value .tru := Value.tru
example : Value .fls := Value.fls
example : ¬ Value (.var 0) := by intro h; cases h
example : ¬ Value (.app .tru .tru) := by intro h; cases h
example : ¬ Value (.ite .tru .tru .tru) := by intro h; cases h
-- The reduction rules must be the original ones.
example : ∀ {A : Ty} {t v : Term}, Value v → Step (.app (.lam A t) v) (subst (subst1 v) t) := @Step.beta
example : ∀ {f f' a : Term}, Step f f' → Step (.app f a) (.app f' a) := @Step.app1
example : ∀ {v a a' : Term}, Value v → Step a a' → Step (.app v a) (.app v a') := @Step.app2
example : ∀ {t e : Term}, Step (.ite .tru t e) t := @Step.iteTrue
example : ∀ {t e : Term}, Step (.ite .fls t e) e := @Step.iteFalse
example : ∀ {c c' t e : Term}, Step c c' → Step (.ite c t e) (.ite c' t e) := @Step.ite
example : ∀ t, ¬ Step .tru t := by intro t h; cases h
example : ∀ t, ¬ Step .fls t := by intro t h; cases h
example : ∀ t, ¬ Step (.var 0) t := by intro t h; cases h
example : ∀ t, ¬ Step (.lam .bool (.app .tru .tru)) t := by intro t h; cases h
example : ∀ t, ¬ Step (.app .tru .fls) t := by
  intro t h
  cases h with
  | app1 h => cases h
  | app2 _ h => cases h
example : ∀ t, ¬ Step (.ite (.lam .bool (.var 0)) .tru .fls) t := by
  intro t h
  cases h with
  | ite h => cases h
-- Renaming and substitution must compute as before.
example : ext (· + 3) 0 = 0 := rfl
example : ext (· + 3) 2 = 5 := rfl
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename Nat.succ (.ite (.var 0) (.var 1) .tru) = .ite (.var 1) (.var 2) .tru := rfl
example : exts (fun n => .var (n + 7)) 0 = .var 0 := rfl
example : exts (fun n => .var (n + 7)) 2 = .var 9 := rfl
example : subst (subst1 .tru) (.lam .bool (.app (.var 1) (.var 0))) = .lam .bool (.app .tru (.var 0)) := rfl
example : subst (subst1 (.var 0)) (.lam .bool (.var 1)) = .lam .bool (.var 1) := rfl
example : subst (subst1 .fls) (.ite (.var 0) (.var 1) .tru) = .ite .fls (.var 0) .tru := rfl
example : subst (fun n => .var (n + 10)) (.lam .bool (.app (.var 0) (.var 2))) = .lam .bool (.app (.var 0) (.var 12)) := rfl
-- The interpreter must compute as before.
example : eval 20 (.app (.app twiceB notB) .tru) = .tru := rfl
example : eval 20 (.app (.app twiceB notB) .fls) = .fls := rfl
example : eval 1 (.app (.lam .bool (.var 0)) .tru) = .tru := rfl
example : eval 0 (.app (.lam .bool (.var 0)) .tru) = .app (.lam .bool (.var 0)) .tru := rfl
example : eval 5 (.ite (.app (.lam .bool (.var 0)) .fls) .fls .tru) = .tru := rfl
example : step (.app .tru .fls) = none := rfl
example : step (.var 0) = none := rfl
example : step (.lam .bool (.app (.lam .bool (.var 0)) .tru)) = none := rfl
example : isValue (.app (.lam .bool (.var 0)) .tru) = false := rfl
