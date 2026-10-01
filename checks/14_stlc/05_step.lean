/- HINT
`run_const` takes three steps: β-reduce the inner application (inside `app1`),
then reduce the argument `pred zero` (inside `app2`, the function is now the value
`lam .nat .tru`), then β again. `apply Star.step (...)` peels off one step.

`value_no_step`: `induction hv generalizing t`. In most cases `intro hs; cases hs`
finds no applicable rule. For `succ`, the only rule is `Step.succ`, and the
induction hypothesis rules out its premise.

`stuck_example`: `constructor`, then `cases` on the hypotheses. For the step part,
the only candidates are `app1` and `app2`, whose premises are steps of `tru` / `zero`.
-/

example : Step (.app (.lam .nat (.succ (.var 0))) .zero) (.succ .zero) := step_beta
example : Star Step (.app (.app (.lam .bool (.lam .nat (.var 1))) .tru) (.pred .zero)) .tru := run_const
example : ∀ {v t : Term}, Value v → ¬ Step v t := @value_no_step
example : ¬ Value (.app .tru .zero) ∧ ∀ t, ¬ Step (.app .tru .zero) t := stuck_example
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
