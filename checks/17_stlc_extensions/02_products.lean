/- HINT
`canonical_prod` works like `canonical_arrow`: `cases hv`, and the
wildcard case `| _ => cases ht` handles the values of the wrong type.

`progress`, `pair` case: two nested `rcases` as for `app` (first `a`, then `b`).
If both are values, the pair is a value: `Or.inl (.pair hva hvb)`.
`fst`/`snd`: if `t` is a value, `obtain ⟨a, b, rfl, ha, hb⟩ := canonical_prod h hv`.

`preservation`, `fstPair` case: invert the typing of the pair with
`cases h with | pair ha _ => …`. Congruence cases rebuild the derivation.

`swap_typed`: build the derivation by hand, e.g. `.lam (.pair … …)`, where
variables are `.var rfl`.
-/

example : ∀ {Γ : Ctx} {v : Term} {A B : Ty}, HasType Γ v (.prod A B) → Value v → ∃ a b, v = .pair a b ∧ Value a ∧ Value b := @canonical_prod
example : ∀ {t : Term} {T : Ty}, HasType [] t T → Value t ∨ ∃ t', Step t t' := @progress
example : ∀ {Γ : Ctx} {t t' : Term} {T : Ty}, HasType Γ t T → Step t t' → HasType Γ t' T := @preservation
example : ∀ {t t' : Term} {T : Ty}, HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := @type_safety
example : ∀ A B : Ty, HasType [] (swap A B) (.prod A B ⇒ .prod B A) := swap_typed
example : Star Step (.app (swap .bool .bool) (.pair .tru .fls)) (.pair .fls .tru) :=
  .step (.beta (.pair .tru .fls))
    (.step (.pair1 (.sndPair .tru .fls))
      (.step (.pair2 .fls (.fstPair .tru .fls)) (.refl _)))
-- The typing rules must be the original ones.
example : ∀ {Γ : Ctx} {x : Nat} {A : Ty}, Γ[x]? = some A → HasType Γ (.var x) A := @HasType.var
example : ∀ {Γ : Ctx} {A : Ty} {t : Term} {B : Ty}, HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B) := @HasType.lam
example : ∀ {Γ : Ctx} {f a : Term} {A B : Ty}, HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B := @HasType.app
example : ∀ {Γ : Ctx}, HasType Γ .tru .bool := @HasType.tru
example : ∀ {Γ : Ctx}, HasType Γ .fls .bool := @HasType.fls
example : ∀ {Γ : Ctx} {c t e : Term} {A : Ty}, HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A := @HasType.ite
example : ∀ {Γ : Ctx} {a b : Term} {A B : Ty}, HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (.prod A B) := @HasType.pair
example : ∀ {Γ : Ctx} {t : Term} {A B : Ty}, HasType Γ t (.prod A B) → HasType Γ (.fst t) A := @HasType.fst
example : ∀ {Γ : Ctx} {t : Term} {A B : Ty}, HasType Γ t (.prod A B) → HasType Γ (.snd t) B := @HasType.snd
example : ¬ HasType [] (.app .tru .fls) .bool := by
  intro h
  cases h with
  | app h _ => cases h
example : ¬ HasType [] (.var 0) .bool := by
  intro h
  cases h with
  | var h => cases h
example : ¬ HasType [] (.fst .tru) .bool := by
  intro h
  cases h with
  | fst h => cases h
example : ¬ HasType [] (.pair .tru .fls) .bool := by intro h; cases h
-- The values must be the original ones.
example : ∀ {A : Ty} {t : Term}, Value (.lam A t) := @Value.lam
example : Value .tru := Value.tru
example : Value .fls := Value.fls
example : ∀ {v w : Term}, Value v → Value w → Value (.pair v w) := @Value.pair
example : ¬ Value (.var 0) := by intro h; cases h
example : ¬ Value (.app .tru .tru) := by intro h; cases h
example : ¬ Value (.fst (.pair .tru .tru)) := by intro h; cases h
example : ¬ Value (.pair (.var 0) .tru) := by intro h; cases h with | pair h _ => cases h
example : ¬ Value (.pair .tru (.var 0)) := by intro h; cases h with | pair _ h => cases h
-- The reduction rules must be the original ones.
example : ∀ {A : Ty} {t v : Term}, Value v → Step (.app (.lam A t) v) (subst (subst1 v) t) := @Step.beta
example : ∀ {f f' a : Term}, Step f f' → Step (.app f a) (.app f' a) := @Step.app1
example : ∀ {v a a' : Term}, Value v → Step a a' → Step (.app v a) (.app v a') := @Step.app2
example : ∀ {t e : Term}, Step (.ite .tru t e) t := @Step.iteTrue
example : ∀ {t e : Term}, Step (.ite .fls t e) e := @Step.iteFalse
example : ∀ {c c' t e : Term}, Step c c' → Step (.ite c t e) (.ite c' t e) := @Step.ite
example : ∀ {a a' b : Term}, Step a a' → Step (.pair a b) (.pair a' b) := @Step.pair1
example : ∀ {v b b' : Term}, Value v → Step b b' → Step (.pair v b) (.pair v b') := @Step.pair2
example : ∀ {v w : Term}, Value v → Value w → Step (.fst (.pair v w)) v := @Step.fstPair
example : ∀ {v w : Term}, Value v → Value w → Step (.snd (.pair v w)) w := @Step.sndPair
example : ∀ {t t' : Term}, Step t t' → Step (.fst t) (.fst t') := @Step.fst
example : ∀ {t t' : Term}, Step t t' → Step (.snd t) (.snd t') := @Step.snd
example : ∀ t, ¬ Step .tru t := by intro t h; cases h
example : ∀ t, ¬ Step (.lam .bool (.fst .tru)) t := by intro t h; cases h
example : ∀ t, ¬ Step (.pair .tru .fls) t := by
  intro t h
  cases h with
  | pair1 h => cases h
  | pair2 _ h => cases h
example : ∀ t, ¬ Step (.fst .tru) t := by
  intro t h
  cases h with
  | fst h => cases h
example : ∀ t, ¬ Step (.snd (.pair (.var 0) .tru)) t := by
  intro t h
  cases h with
  | sndPair h _ => cases h
  | snd h =>
    cases h with
    | pair1 h => cases h
    | pair2 h _ => cases h
-- Renaming and substitution must compute as before.
example : rename (· + 5) (.app (.lam .bool (.lam .bool (.var 2))) (.var 3)) = .app (.lam .bool (.lam .bool (.var 7))) (.var 8) := rfl
example : rename (· + 5) (.pair (.fst (.var 0)) (.lam .bool (.snd (.var 1)))) = .pair (.fst (.var 5)) (.lam .bool (.snd (.var 6))) := rfl
example : subst (subst1 .tru) (.lam .bool (.app (.var 1) (.var 0))) = .lam .bool (.app .tru (.var 0)) := rfl
example : subst (subst1 .tru) (.pair (.fst (.var 0)) (.lam .bool (.snd (.var 1)))) = .pair (.fst .tru) (.lam .bool (.snd .tru)) := rfl
