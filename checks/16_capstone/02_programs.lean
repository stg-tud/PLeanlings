/- HINT
`compose`: the body sits under three binders, so `f` is `var 2`, `g` is `var 1` and
`x` is `var 0`. The typing derivation is `.lam (.lam (.lam (.app … …)))`, with
`.var rfl` for each variable.

`isOne n = if iszero n then false else iszero (pred n)`.
`andFn a b = if a then b else false`.
-/

example : ∀ A B C : Ty, HasType [] (compose A B C) ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) := compose_typed
example : HasType [] isOne (.nat ⇒ .bool) := isOne_typed
example : typeOf [] (compose .nat .bool .nat) = some ((.bool ⇒ .nat) ⇒ (.nat ⇒ .bool) ⇒ .nat ⇒ .nat) := rfl
example : typeOf [] andFn = some (.bool ⇒ .bool ⇒ .bool) := rfl
example : eval 100 (.app (.app (.app (compose .nat .nat .nat) succFn) succFn) .zero) = Term.num 2 := rfl
example : eval 100 (.app (.app (.app (compose .bool .bool .bool) notFn) (.lam .bool .fls)) .fls) = .tru := rfl
example : eval 100 (.app isOne (Term.num 0)) = .fls := rfl
example : eval 100 (.app isOne (Term.num 1)) = .tru := rfl
example : eval 100 (.app isOne (Term.num 2)) = .fls := rfl
example : eval 100 (.app isOne (Term.num 5)) = .fls := rfl
example : eval 100 (.app (.app andFn .tru) .tru) = .tru := rfl
example : eval 100 (.app (.app andFn .tru) .fls) = .fls := rfl
example : eval 100 (.app (.app andFn .fls) .tru) = .fls := rfl
example : eval 100 (.app (.app andFn .fls) .fls) = .fls := rfl
example : eval 100 (.app (.app andFn .fls) (.app notFn .fls)) = .fls := rfl
example : ∀ {t t' : Term} {T : Ty}, HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := @type_safety
-- The type checker must compute as before.
example : typeOf [.bool] (.var 0) = some .bool := rfl
example : typeOf [] (.var 0) = none := rfl
example : typeOf [] (.lam .nat (.succ (.var 0))) = some (.nat ⇒ .nat) := rfl
example : typeOf [] (.app (.lam .nat (.var 0)) .zero) = some .nat := rfl
example : typeOf [] (.app (.lam .nat (.var 0)) .tru) = none := rfl
example : typeOf [] (.app .zero .tru) = none := rfl
example : typeOf [] (.ite .tru .zero (.succ .zero)) = some .nat := rfl
example : typeOf [] (.ite .tru .zero .fls) = none := rfl
example : typeOf [] (.ite .zero .zero .zero) = none := rfl
example : typeOf [] (.pred (.iszero .zero)) = none := rfl
example : typeOf [] (.iszero (.pred .zero)) = some .bool := rfl
example : typeOf [] (.succ .fls) = none := rfl
example : typeOf [] (.iszero .tru) = none := rfl
example : typeOf [] .fls = some .bool := rfl
-- The step function must compute as before.
example : step (.app (.lam .nat (.succ (.var 0))) .zero) = some (.succ .zero) := rfl
example : step (.app (.lam .nat (.var 0)) (.pred .zero)) = some (.app (.lam .nat (.var 0)) .zero) := rfl
example : step (.app (.app (.lam .bool (.lam .nat (.var 1))) .tru) .zero) = some (.app (.lam .nat .tru) .zero) := rfl
example : step (.app .tru .zero) = none := rfl
example : step (.ite .tru .zero .fls) = some .zero := rfl
example : step (.ite (.iszero .zero) .zero .fls) = some (.ite .tru .zero .fls) := rfl
example : step (.pred (.succ .zero)) = some .zero := rfl
example : step (.iszero (.succ .zero)) = some .fls := rfl
example : step (.succ (.pred .zero)) = some (.succ .zero) := rfl
example : step (.lam .nat (.pred .zero)) = none := rfl
example : isValue (.succ (.succ .zero)) = true := rfl
example : isValue (.succ (.var 0)) = false := rfl
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
