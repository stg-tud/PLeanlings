/- HINT
`progress`: if `t` is a value, `canonical_arrow h hv` says it is a `lam`
(`obtain ⟨b, rfl⟩ := …`), and `fixBeta` applies. `preservation`, `fixBeta` case:
invert the typing of the function (`cases h with | lam hb => …`) and use
`subst1_typing`. Which term is substituted, and what is its type?

`loop_step` is a single rule (`subst (subst1 loop) (var 0)` computes to
`loop`). For `loop_step_inv`, `cases h`; the congruence case is impossible
since a `lam` does not step. `loop_star`: induction on the `Star` derivation.
`loop_diverges`: rewrite with `loop_star hs rfl`, then note that `loop` is
not a value. `not_normalizing` is one line from `loop_diverges` and `loop_typed`.

`mult` follows the pattern of `plus`, with `plus` used inside the body (it is
a closed term, so it means the same under any number of binders).
For `mult_typed`, `plus_typed _` types the inner `plus`.
-/

example : ∀ {t : Term} {T : Ty}, HasType [] t T → Value t ∨ ∃ t', Step t t' := @progress
example : ∀ {Γ : Ctx} {t t' : Term} {T : Ty}, HasType Γ t T → Step t t' → HasType Γ t' T := @preservation
example : ∀ {t t' : Term} {T : Ty}, HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := @type_safety
example : loop = .fix (.lam .nat (.var 0)) := rfl
example : HasType [] loop .nat := loop_typed
example : Step loop loop := loop_step
example : ∀ {t : Term}, Step loop t → t = loop := @loop_step_inv
example : ∀ {s t : Term}, Star Step s t → s = loop → t = loop := @loop_star
example : ¬ ∃ v, Star Step loop v ∧ Value v := loop_diverges
example : ¬ ∀ t T, HasType [] t T → ∃ v, Star Step t v ∧ Value v := not_normalizing
example : HasType [] mult (.nat ⇒ .nat ⇒ .nat) := mult_typed
#guard (eval 10000 (.app (.app mult (Term.num 3)) (Term.num 4))).toNat? == some 12
#guard (eval 10000 (.app (.app mult (Term.num 0)) (Term.num 4))).toNat? == some 0
#guard (eval 10000 (.app (.app mult (Term.num 4)) (Term.num 0))).toNat? == some 0
#guard (eval 10000 (.app (.app mult (Term.num 2)) (Term.num 5))).toNat? == some 10
#guard (eval 10000 (.app (.app plus (Term.num 2)) (Term.num 5))).toNat? == some 7
-- The new rules.
example : ∀ {Γ : Ctx} {t : Term} {A : Ty}, HasType Γ t (A ⇒ A) → HasType Γ (.fix t) A := @HasType.fix
example : ∀ {A : Ty} {b : Term}, Step (.fix (.lam A b)) (subst (subst1 (.fix (.lam A b))) b) := @Step.fixBeta
example : ∀ {t t' : Term}, Step t t' → Step (.fix t) (.fix t') := @Step.fix
example : ¬ HasType [] (.fix (.lam .nat .tru)) .nat := by
  intro h
  cases h with
  | fix h => cases h with | lam h => cases h
example : ¬ Value (.fix (.lam .nat (.var 0))) := by intro h; cases h
example : ∀ t, ¬ Step (.fix .tru) t := by
  intro t h
  cases h with
  | fix h => cases h
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
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename (· + 5) (.fix (.lam .nat (.app (.var 0) (.var 1)))) = .fix (.lam .nat (.app (.var 0) (.var 6))) := rfl
example : subst (subst1 .tru) (.lam .nat (.app (.var 1) (.var 0))) = .lam .nat (.app .tru (.var 0)) := rfl
example : subst (subst1 .zero) (.fix (.lam .nat (.app (.var 0) (.var 1)))) = .fix (.lam .nat (.app (.var 0) .zero)) := rfl
example : step (.fix (.lam .nat (.succ (.var 0)))) = some (.succ (.fix (.lam .nat (.succ (.var 0))))) := rfl
example : step loop = some loop := rfl
