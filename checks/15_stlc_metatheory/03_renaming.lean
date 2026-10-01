/- HINT
`ext_ok`: `intro x A hx` and `cases x with | zero => … | succ n => …`. Both
cases close with a single `exact`: in the `zero` case the hypothesis already
is the goal (up to computation), in the `succ` case use `hρ`.

In `rename_typing`, look at the `app` case: the induction hypotheses take the
well-typedness of the renaming as argument. For `var`, use `hρ` and `.var`;
for `lam`, call the induction hypothesis with `ext_ok hρ`.

`weakening` is `rename_typing` applied to a proof that `Nat.succ` is
well-typed from `Γ` to `B :: Γ`. That proof is `fun _ _ h => h`. Why?
-/

example : ∀ {Γ Δ : Ctx} {ρ : Nat → Nat} {B : Ty}, (∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) → ∀ x A, (B :: Γ)[x]? = some A → (B :: Δ)[ext ρ x]? = some A := @ext_ok
example : ∀ {Γ Δ : Ctx} {ρ : Nat → Nat} {t : Term} {T : Ty}, (∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) → HasType Γ t T → HasType Δ (rename ρ t) T := @rename_typing
example : ∀ {Γ : Ctx} {t : Term} {T B : Ty}, HasType Γ t T → HasType (B :: Γ) (rename Nat.succ t) T := @weakening
-- The typing rules must be the original ones.
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
-- The reduction rules must be the original ones.
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
-- Renaming and substitution must compute as before.
example : ext (· + 3) 0 = 0 := rfl
example : ext (· + 3) 2 = 5 := rfl
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename Nat.succ (.ite (.var 0) (.succ (.var 1)) (.iszero (.pred .zero))) = .ite (.var 1) (.succ (.var 2)) (.iszero (.pred .zero)) := rfl
example : exts (fun n => .var (n + 7)) 0 = .var 0 := rfl
example : exts (fun n => .var (n + 7)) 2 = .var 9 := rfl
example : subst (subst1 .tru) (.lam .nat (.app (.var 1) (.var 0))) = .lam .nat (.app .tru (.var 0)) := rfl
example : subst (subst1 (.var 0)) (.lam .nat (.var 1)) = .lam .nat (.var 1) := rfl
example : subst (subst1 .zero) (.ite (.var 0) (.succ (.var 1)) (.iszero (.pred .fls))) = .ite .zero (.succ (.var 0)) (.iszero (.pred .fls)) := rfl
