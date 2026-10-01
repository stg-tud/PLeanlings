/- HINT
Build derivations from the conclusion upwards: the outermost term former tells
you which rule to apply. Variable premises are solved by `rfl`. For `typed_twice`
the context in the body is `[.nat, .nat ⇒ .nat]`. In tactic mode, `apply
HasType.app` may leave the argument type as a metavariable `?A`, which gets
filled in when you solve the first subgoal.

For the negative statements: `intro T h`, then `cases h with | app hf _ => ...`.
What could `hf : HasType [] .tru (?A ⇒ T)` possibly be? A further `cases`
answers "nothing". For the variable, `cases` the lookup equation
`[][0]? = some T`.
-/

example : HasType [] (.lam .nat (.lam .bool (.var 1))) (.nat ⇒ .bool ⇒ .nat) := typed_const
example : HasType [.nat, .nat ⇒ .bool] (.app (.var 1) (.succ (.var 0))) .bool := typed_open
example : HasType [] twice ((.nat ⇒ .nat) ⇒ .nat ⇒ .nat) := typed_twice
example : twice = .lam (.arrow .nat .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0)))) := rfl
example : ∀ T, ¬ HasType [] (.app .tru .zero) T := untyped_app
example : ∀ T, ¬ HasType [] (.var 0) T := untyped_var
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
