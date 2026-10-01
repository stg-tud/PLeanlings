/- HINT
All four are inductions on a reduction sequence: `intro …`, then
`induction h with | refl => … | step h _ ih => …`. For `star_trans`,
induct on the *first* sequence.

`star_app2` and `star_ite` are copies of `star_app1` with a different rule
(`.app2 hv h`, `.ite h`). `halts_back`: take the witness apart with
`obtain ⟨v, hv, hval⟩ := h` and give `⟨v, .step hs hv, hval⟩`.
-/

example : ∀ {t u w : Term}, Star Step t u → Star Step u w → Star Step t w := @star_trans
example : ∀ {f f' a : Term}, Star Step f f' → Star Step (.app f a) (.app f' a) := @star_app1
example : ∀ {v a a' : Term}, Value v → Star Step a a' → Star Step (.app v a) (.app v a') := @star_app2
example : ∀ {c c' t e : Term}, Star Step c c' → Star Step (.ite c t e) (.ite c' t e) := @star_ite
example : ∀ {v : Term}, Value v → Halts v := @value_halts
example : ∀ {t t' : Term}, Step t t' → Halts t' → Halts t := @halts_back
-- `Halts` must be the original definition.
example : ∀ t, Halts t = ∃ v, Star Step t v ∧ Value v := fun _ => rfl
example : ∀ {α : Type} {R : α → α → Prop} (a : α), Star R a a := @Star.refl
example : ∀ {α : Type} {R : α → α → Prop} {a b c : α}, R a b → Star R b c → Star R a c := @Star.step
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
