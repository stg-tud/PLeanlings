/- HINT
`subst_subst`, case `n + 1`: both sides equal
`subst (fun x => rename Nat.succ (τ x)) (σ n)`, the left side by
`subst_rename (fun _ => rfl)`, the right side by `rename_subst (fun _ => rfl)`.
State both with `have` and `rw`.

`subst_id`: like the others; the `succ n` case is `simp [exts, h, rename]`.

`subst1_exts`: `apply subst_subst`, `intro x`, `cases x`. Case `zero` is `rfl`.
For `succ n`, show `subst (subst1 v) (rename Nat.succ (σ n)) = subst Term.var (σ n)` by
`subst_rename (fun _ => rfl)`, then `subst_id (fun _ => rfl)`.
-/

example : ∀ {σ τ υ : Nat → Term} {t : Term}, (∀ x, subst τ (σ x) = υ x) → subst τ (subst σ t) = subst υ t := @subst_subst
example : ∀ {σ : Nat → Term} {t : Term}, (∀ x, σ x = .var x) → subst σ t = t := @subst_id
example : ∀ {v : Term} {σ : Nat → Term} {t : Term}, subst (subst1 v) (subst (exts σ) t) = subst (scons v σ) t := @subst1_exts
example : ∀ {ρ ρ' ρ'' : Nat → Nat} {t : Term}, (∀ x, ρ (ρ' x) = ρ'' x) → rename ρ (rename ρ' t) = rename ρ'' t := @rename_rename
example : ∀ {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}, (∀ x, σ (ρ x) = τ x) → subst σ (rename ρ t) = subst τ t := @subst_rename
example : ∀ {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}, (∀ x, rename ρ (σ x) = τ x) → rename ρ (subst σ t) = subst τ t := @rename_subst
-- `scons` must compute as before.
example : ∀ v σ, scons v σ 0 = v := fun _ _ => rfl
example : ∀ v σ n, scons v σ (n + 1) = σ n := fun _ _ _ => rfl
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
