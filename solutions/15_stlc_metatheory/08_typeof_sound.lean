/-
# 15.08 — The type checker is sound

In chapter 14 you wrote `typeOf : Ctx → Term → Option Ty`. Now we prove that
it is correct. First **soundness**: if the checker says `T`, then there is a
typing derivation.

    theorem typeOf_sound : typeOf Γ t = some T → HasType Γ t T

**Proof.** By induction on the term `t` (not on a derivation, since we don't have one
yet!), generalizing `Γ` and `T`. In each case we look at the results of the
recursive calls with `cases hB : typeOf (A :: Γ) t with …`. This names the
equation `hB`, which we feed to `simp [typeOf, hB] at h` to compute what `typeOf`
returned. If a recursive call failed, `h` becomes `none = some T`, which `simp`
recognizes as `False` and closes the goal. Otherwise `h` becomes an equation like
`A ⇒ B = T`, which we use to rewrite the goal.

For the application case we also need to case on the *shape* of the function type
(`cases F with | arrow A B => … | _ => …`). After `simp`, the hypothesis is
`A = A' ∧ B = T`, and `obtain ⟨rfl, rfl⟩ := h` substitutes both equations.

## Your task

Complete the `app`, `ite` and `iszero` cases. The `lam` and `succ` cases are
your models.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Types: `T ::= bool | nat | T ⇒ T`. -/
inductive Ty where
  | bool
  | nat
  | arrow (A B : Ty)
  deriving DecidableEq, Repr

/-- `A ⇒ B` is the function type. It associates to the right. -/
infixr:70 " ⇒ " => Ty.arrow

/-- Terms with de Bruijn indices. `lam A t` binds variable `0` (of type `A`) in `t`. -/
inductive Term where
  | var (x : Nat)
  | lam (A : Ty) (body : Term)
  | app (f a : Term)
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving DecidableEq, Repr

/-- A context lists the types of the free variables: `Γ[0]?` is the type of `var 0`. -/
abbrev Ctx := List Ty

/-- `HasType Γ t T` means `Γ ⊢ t : T`. -/
/-
    Γ[x]? = some A           A :: Γ ⊢ t : B             Γ ⊢ f : A ⇒ B    Γ ⊢ a : A
  ─────────────── var    ──────────────────── lam    ──────────────────────────── app
   Γ ⊢ var x : A          Γ ⊢ lam A t : A ⇒ B                Γ ⊢ app f a : B

  ───────────────── tru   ───────────────── fls
   Γ ⊢ tru : bool          Γ ⊢ fls : bool

   Γ ⊢ c : bool    Γ ⊢ t : A    Γ ⊢ e : A
  ───────────────────────────────────────── ite
          Γ ⊢ ite c t e : A

                         Γ ⊢ t : nat              Γ ⊢ t : nat             Γ ⊢ t : nat
  ───────────── zero   ───────────────── succ   ───────────────── pred  ──────────────────── iszero
   Γ ⊢ zero : nat       Γ ⊢ succ t : nat         Γ ⊢ pred t : nat       Γ ⊢ iszero t : bool
-/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (.var x) A
  | lam {Γ A t B} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ c t e A} : HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A
  | zero {Γ} : HasType Γ .zero .nat
  | succ {Γ t} : HasType Γ t .nat → HasType Γ (.succ t) .nat
  | pred {Γ t} : HasType Γ t .nat → HasType Γ (.pred t) .nat
  | iszero {Γ t} : HasType Γ t .nat → HasType Γ (.iszero t) .bool

/-- Lift a renaming under a binder: `0` stays `0`, `n + 1` becomes `ρ n + 1`. -/
def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply the renaming `ρ` to all free variables. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .var x => .var (ρ x)
  | .lam A t => .lam A (rename (ext ρ) t)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .pred t => .pred (rename ρ t)
  | .iszero t => .iszero (rename ρ t)

/-- Lift a substitution under a binder. -/
def exts (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Parallel substitution: replace every free variable `x` by `σ x`. -/
def subst (σ : Nat → Term) : Term → Term
  | .var x => σ x
  | .lam A t => .lam A (subst (exts σ) t)
  | .app f a => .app (subst σ f) (subst σ a)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .pred t => .pred (subst σ t)
  | .iszero t => .iszero (subst σ t)

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions, booleans and numerals. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls
  | zero : Value .zero
  | succ {v} : Value v → Value (.succ v)

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
/-
          Value v                              f ⟶ f'                     Value v    a ⟶ a'
  ──────────────────────────────── beta   ────────────────── app1   ──────────────────────── app2
   app (lam A t) v ⟶ t[v]                  app f a ⟶ app f' a       app v a ⟶ app v a'

  ─────────────────────── iteTrue   ─────────────────────── iteFalse         c ⟶ c'
   ite tru t e ⟶ t                   ite fls t e ⟶ e                  ──────────────────────────── ite
                                                                        ite c t e ⟶ ite c' t e
       t ⟶ t'                                               Value v                    t ⟶ t'
  ─────────────────── succ  ───────────────── predZero  ──────────────────── predSucc  ─────────────────── pred
   succ t ⟶ succ t'          pred zero ⟶ zero           pred (succ v) ⟶ v              pred t ⟶ pred t'

                                       Value v                            t ⟶ t'
  ───────────────────── iszeroZero  ───────────────────────── iszeroSucc  ─────────────────────── iszero
   iszero zero ⟶ tru                 iszero (succ v) ⟶ fls               iszero t ⟶ iszero t'

  where t[v] = subst (subst1 v) t.
-/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | succ {t t'} : Step t t' → Step (.succ t) (.succ t')
  | predZero : Step (.pred .zero) .zero
  | predSucc {v} : Value v → Step (.pred (.succ v)) v
  | pred {t t'} : Step t t' → Step (.pred t) (.pred t')
  | iszeroZero : Step (.iszero .zero) .tru
  | iszeroSucc {v} : Value v → Step (.iszero (.succ v)) .fls
  | iszero {t t'} : Step t t' → Step (.iszero t) (.iszero t')

/-- The type checker. -/
def typeOf (Γ : Ctx) : Term → Option Ty
  | .var x => Γ[x]?
  | .lam A t =>
    match typeOf (A :: Γ) t with
    | some B => some (A ⇒ B)
    | none => none
  | .app f a =>
    match typeOf Γ f, typeOf Γ a with
    | some (.arrow A B), some A' => if A = A' then some B else none
    | _, _ => none
  | .tru => some .bool
  | .fls => some .bool
  | .ite c t e =>
    match typeOf Γ c, typeOf Γ t, typeOf Γ e with
    | some .bool, some A, some A' => if A = A' then some A else none
    | _, _, _ => none
  | .zero => some .nat
  | .succ t =>
    match typeOf Γ t with
    | some .nat => some .nat
    | _ => none
  | .pred t =>
    match typeOf Γ t with
    | some .nat => some .nat
    | _ => none
  | .iszero t =>
    match typeOf Γ t with
    | some .nat => some .bool
    | _ => none

/-! ## Soundness of `typeOf` -/

theorem typeOf_sound {Γ : Ctx} {t : Term} {T : Ty} :
    typeOf Γ t = some T → HasType Γ t T := by
  induction t generalizing Γ T with
  | var x =>
    intro h
    exact .var h
  | lam A t ih =>
    intro h
    cases hB : typeOf (A :: Γ) t with
    | none => simp [typeOf, hB] at h
    | some B =>
      simp [typeOf, hB] at h
      rw [← h]
      exact .lam (ih hB)
  | app f a ihf iha =>
    intro h
    cases hf : typeOf Γ f with
    | none => simp [typeOf, hf] at h
    | some F =>
      cases ha : typeOf Γ a with
      | none => simp [typeOf, hf, ha] at h
      | some A' =>
        cases F with
        | arrow A B =>
          simp [typeOf, hf, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app (ihf hf) (iha ha)
        | _ => simp [typeOf, hf, ha] at h
  | tru =>
    intro h
    simp [typeOf] at h
    rw [← h]
    exact .tru
  | fls =>
    intro h
    simp [typeOf] at h
    rw [← h]
    exact .fls
  | ite c t e ihc iht ihe =>
    intro h
    cases hc : typeOf Γ c with
    | none => simp [typeOf, hc] at h
    | some C =>
      cases ht : typeOf Γ t with
      | none => simp [typeOf, hc, ht] at h
      | some A =>
        cases he : typeOf Γ e with
        | none => simp [typeOf, hc, ht, he] at h
        | some A' =>
          cases C with
          | bool =>
            simp [typeOf, hc, ht, he] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .ite (ihc hc) (iht ht) (ihe he)
          | _ => simp [typeOf, hc, ht, he] at h
  | zero =>
    intro h
    simp [typeOf] at h
    rw [← h]
    exact .zero
  | succ t ih =>
    intro h
    cases ht : typeOf Γ t with
    | none => simp [typeOf, ht] at h
    | some A =>
      cases A with
      | nat =>
        simp [typeOf, ht] at h
        rw [← h]
        exact .succ (ih ht)
      | _ => simp [typeOf, ht] at h
  | pred t ih =>
    intro h
    cases ht : typeOf Γ t with
    | none => simp [typeOf, ht] at h
    | some A =>
      cases A with
      | nat =>
        simp [typeOf, ht] at h
        rw [← h]
        exact .pred (ih ht)
      | _ => simp [typeOf, ht] at h
  | iszero t ih =>
    intro h
    cases ht : typeOf Γ t with
    | none => simp [typeOf, ht] at h
    | some A =>
      cases A with
      | nat =>
        simp [typeOf, ht] at h
        rw [← h]
        exact .iszero (ih ht)
      | _ => simp [typeOf, ht] at h
