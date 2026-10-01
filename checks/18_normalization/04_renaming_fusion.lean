/- HINT
`subst_rename` is `rename_rename` with `subst` added to the `simp` lists; in the
`lam` case, `succ n` is `simp [ext, exts, h]`.

`rename_subst`, case `n + 1`: the goal is
`rename (ext ρ) (rename Nat.succ (σ n)) = rename Nat.succ (rename ρ (σ n))`.
```
have e1 : rename (ext ρ) (rename Nat.succ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
  rename_rename (fun _ => rfl)
```
then the same for the right-hand side, and `rw [e1, e2]`.
-/

example : ∀ {ρ ρ' ρ'' : Nat → Nat} {t : Term}, (∀ x, ρ (ρ' x) = ρ'' x) → rename ρ (rename ρ' t) = rename ρ'' t := @rename_rename
example : ∀ {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}, (∀ x, σ (ρ x) = τ x) → subst σ (rename ρ t) = subst τ t := @subst_rename
example : ∀ {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}, (∀ x, rename ρ (σ x) = τ x) → rename ρ (subst σ t) = subst τ t := @rename_subst
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
