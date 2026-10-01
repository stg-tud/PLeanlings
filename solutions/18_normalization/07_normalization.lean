/-
# 18.07 — Normalization

Everything is in place. A closed term is instantiated by the identity
substitution `Term.var`. The condition `Inst [] Term.var` holds trivially,
because `[]` has no variables. So the fundamental lemma gives
`R T (subst Term.var t)`, `subst_id` turns that into `R T t`, and `R_halts`
concludes:

    theorem normalization : HasType [] t T → Halts t

As a corollary, the fuel-based interpreter `eval` from chapter 16 (restricted to
our smaller language) always reaches a value if given enough fuel. For that we
need that the interpreter can follow every step of the relation, which is
`step_complete` (given below; it is chapter 15's `step_sound` in the other
direction). Then by induction on `t ⟶* v`:

    theorem eval_of_star : Star Step t v → Value v → ∃ n, eval n t = v

## Your task

Prove `normalization`, `eval_of_star` and `eval_terminates`.

## Where the proof breaks with `fix`

With chapter 17's `fix`, `fix (λx:T. x)` is well-typed at every `T`, and
`fix (λx:T. x) ⟶ fix (λx:T. x) ⟶ …` diverges. So the theorem is false, and the
proof must break somewhere. Everything except the fundamental lemma is
unaffected. Its new case reads

    Γ ⊢ f : T ⇒ T
    ──────────────    show: R T (subst σ (fix f)),  knowing: R (T ⇒ T) (subst σ f)
    Γ ⊢ fix f : T

The only way to use the induction hypothesis is to apply `subst σ f` to a reducible
argument of type `T`. But the only candidate is `fix (subst σ f)` itself, and
its reducibility is exactly what we want to prove. The argument is circular. No
other property of `R` can rescue it either, since `R T` implies halting.

## Beyond: strong normalization

We proved *weak* normalization for *one* strategy: CBV reduction of closed
terms reaches a value. **Strong normalization** says that *every* sequence of
full β-reductions terminates, in any order and even under `λ`, so on open terms too.
The same idea works, but the relation needs more care (Girard's
*reducibility candidates*): `R T` is required to satisfy three
conditions, usually called CR1–CR3:

* CR1: reducible terms are strongly normalizing;
* CR2: `R T` is closed under reduction;
* CR3: a *neutral* term (not a `λ`) all of whose one-step reducts are reducible
  is itself reducible. In particular, all variables are reducible.

They are proven together by induction on `T`, and the fundamental lemma is
then proven as before. Girard extended this method to System F (polymorphic λ-calculus),
where `R` cannot be defined by recursion on types anymore and one quantifies over
*all* candidate sets instead. See Girard, Lafont, Taylor, *Proofs and Types*, chapters 6 and 14.

Normalization also matters for logic. Under Curry–Howard, a normalizing type
theory has no closed proof of `False`. For proof assistants like Lean,
consistency arguments of this kind use the same logical-relations ideas, on a much
larger scale.

# Congratulations!

You have proven a real theorem of PL metatheory that needs more than "induction
on the derivation". You strengthened the induction hypothesis to a type-indexed
logical relation, generalized to open terms via instantiations, and paid the de Bruijn
bill with a small substitution algebra. This is the end of Leanlings. Well done!
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types of this chapter: `T ::= bool | T ⇒ T` (no `nat`). -/
inductive Ty where
  | bool
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
-/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (.var x) A
  | lam {Γ A t B} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B
  | tru {Γ} : HasType Γ .tru .bool
  | fls {Γ} : HasType Γ .fls .bool
  | ite {Γ c t e A} : HasType Γ c .bool → HasType Γ t A → HasType Γ e A → HasType Γ (.ite c t e) A

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

/-- Single substitution: `subst (subst1 s) t` replaces `var 0` by `s`
and renumbers the other free variables down by one. -/
def subst1 (s : Term) : Nat → Term
  | 0 => s
  | n + 1 => .var n

/-- Values: λ-abstractions and booleans. -/
inductive Value : Term → Prop where
  | lam {A t} : Value (.lam A t)
  | tru : Value .tru
  | fls : Value .fls

/-- Call-by-value small-step reduction `t ⟶ t'`. -/
/-
          Value v                              f ⟶ f'                     Value v    a ⟶ a'
  ──────────────────────────────── beta   ────────────────── app1   ──────────────────────── app2
   app (lam A t) v ⟶ t[v]                  app f a ⟶ app f' a       app v a ⟶ app v a'

  ─────────────────────── iteTrue   ─────────────────────── iteFalse         c ⟶ c'
   ite tru t e ⟶ t                   ite fls t e ⟶ e                  ──────────────────────────── ite
                                                                        ite c t e ⟶ ite c' t e

  where t[v] = subst (subst1 v) t.
-/
inductive Step : Term → Term → Prop where
  | beta {A t v} : Value v → Step (.app (.lam A t) v) (subst (subst1 v) t)
  | app1 {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | app2 {v a a'} : Value v → Step a a' → Step (.app v a) (.app v a')
  | iteTrue {t e} : Step (.ite .tru t e) t
  | iteFalse {t e} : Step (.ite .fls t e) e
  | ite {c c' t e} : Step c c' → Step (.ite c t e) (.ite c' t e)

/-- `t` halts: it reduces in finitely many steps to a value. -/
def Halts (t : Term) : Prop := ∃ v, Star Step t v ∧ Value v

theorem star_trans {t u w : Term} : Star Step t u → Star Step u w → Star Step t w := by
  intro h1 h2
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem star_app1 {f f' a : Term} : Star Step f f' → Star Step (.app f a) (.app f' a) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.app1 h) ih

theorem star_app2 {v a a' : Term} :
    Value v → Star Step a a' → Star Step (.app v a) (.app v a') := by
  intro hv h
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.app2 hv h) ih

theorem star_ite {c c' t e : Term} : Star Step c c' → Star Step (.ite c t e) (.ite c' t e) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.ite h) ih

theorem value_halts {v : Term} : Value v → Halts v :=
  fun hv => ⟨v, .refl v, hv⟩

theorem halts_back {t t' : Term} : Step t t' → Halts t' → Halts t := by
  intro hs h
  obtain ⟨v, hv, hval⟩ := h
  exact ⟨v, .step hs hv, hval⟩

theorem value_no_step {v t : Term} : Value v → ¬ Step v t := by
  intro hv hs
  cases hv <;> cases hs

theorem step_det {t t₁ t₂ : Term} : Step t t₁ → Step t t₂ → t₁ = t₂ := by
  intro h1 h2
  induction h1 generalizing t₂ with
  | beta hv =>
    cases h2 with
    | beta _ => rfl
    | app1 h => cases h
    | app2 _ h => exact absurd h (value_no_step hv)
  | app1 h ih =>
    cases h2 with
    | beta _ => cases h
    | app1 h' => rw [ih h']
    | app2 hv _ => exact absurd h (value_no_step hv)
  | app2 hv h ih =>
    cases h2 with
    | beta hv' => exact absurd h (value_no_step hv')
    | app1 h' => exact absurd h' (value_no_step hv)
    | app2 _ h' => rw [ih h']
  | iteTrue =>
    cases h2 with
    | iteTrue => rfl
    | ite h => cases h
  | iteFalse =>
    cases h2 with
    | iteFalse => rfl
    | ite h => cases h
  | ite h ih =>
    cases h2 with
    | iteTrue => cases h
    | iteFalse => cases h
    | ite h' => rw [ih h']

theorem star_step_det {t t' v : Term} :
    Star Step t v → Value v → Step t t' → Star Step t' v := by
  intro hs hv h
  cases hs with
  | refl => exact absurd h (value_no_step hv)
  | step h' rest =>
    rw [step_det h h']
    exact rest

theorem halts_fwd {t t' : Term} : Step t t' → Halts t → Halts t' := by
  intro hs h
  obtain ⟨v, hv, hval⟩ := h
  exact ⟨v, star_step_det hv hval hs, hval⟩

/-- The logical relation ("reducibility"), by recursion on the type:

* `R bool t`: `t` reduces to `true` or to `false`;
* `R (A ⇒ B) t`: `t` halts, and applied to any `R A` argument it gives an `R B` result. -/
def R : Ty → Term → Prop
  | .bool, t => Star Step t .tru ∨ Star Step t .fls
  | .arrow A B, t => Halts t ∧ ∀ s, R A s → R B (.app t s)

theorem R_halts {T : Ty} {t : Term} : R T t → Halts t := by
  intro h
  cases T with
  | bool =>
    rcases h with h | h
    · exact ⟨_, h, .tru⟩
    · exact ⟨_, h, .fls⟩
  | arrow A B => exact h.1

theorem R_back {T : Ty} {t t' : Term} : Step t t' → R T t' → R T t := by
  intro hs h
  induction T generalizing t t' with
  | bool =>
    rcases h with h | h
    · exact Or.inl (.step hs h)
    · exact Or.inr (.step hs h)
  | arrow A B _ ihB =>
    exact ⟨halts_back hs h.1, fun s hRs => ihB (.app1 hs) (h.2 s hRs)⟩

theorem R_fwd {T : Ty} {t t' : Term} : Step t t' → R T t → R T t' := by
  intro hs h
  induction T generalizing t t' with
  | bool =>
    rcases h with h | h
    · exact Or.inl (star_step_det h .tru hs)
    · exact Or.inr (star_step_det h .fls hs)
  | arrow A B _ ihB =>
    exact ⟨halts_fwd hs h.1, fun s hRs => ihB (.app1 hs) (h.2 s hRs)⟩

theorem R_star_back {T : Ty} {t t' : Term} : Star Step t t' → R T t' → R T t := by
  intro hs h
  induction hs with
  | refl => exact h
  | step h1 _ ih => exact R_back h1 (ih h)

theorem R_star_fwd {T : Ty} {t t' : Term} : Star Step t t' → R T t → R T t' := by
  intro hs h
  induction hs with
  | refl => exact h
  | step h1 _ ih => exact ih (R_fwd h1 h)

theorem rename_rename {ρ ρ' ρ'' : Nat → Nat} {t : Term} (h : ∀ x, ρ (ρ' x) = ρ'' x) :
    rename ρ (rename ρ' t) = rename ρ'' t := by
  induction t generalizing ρ ρ' ρ'' with
  | var x => simp [rename, h]
  | lam A t ih =>
    simp only [rename]
    rw [ih]
    -- left: the lifted renamings still compose
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [ext, h]
  | app f a ihf iha => simp [rename, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, ihc h, iht h, ihe h]

theorem subst_rename {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}
    (h : ∀ x, σ (ρ x) = τ x) :
    subst σ (rename ρ t) = subst τ t := by
  induction t generalizing σ τ ρ with
  | var x => simp [rename, subst, h]
  | lam A t ih =>
    simp only [rename, subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [ext, exts, h]
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]

theorem rename_subst {σ τ : Nat → Term} {ρ : Nat → Nat} {t : Term}
    (h : ∀ x, rename ρ (σ x) = τ x) :
    rename ρ (subst σ t) = subst τ t := by
  induction t generalizing σ τ ρ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [rename, subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n =>
      -- goal: rename (ext ρ) (exts σ (n + 1)) = exts τ (n + 1)
      simp only [exts, ← h n]
      have e1 : rename (ext ρ) (rename Nat.succ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
        rename_rename (fun _ => rfl)
      have e2 : rename Nat.succ (rename ρ (σ n)) = rename (fun x => ρ x + 1) (σ n) :=
        rename_rename (fun _ => rfl)
      rw [e1, e2]
  | app f a ihf iha => simp [rename, subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [rename, subst, ihc h, iht h, ihe h]

theorem subst_subst {σ τ υ : Nat → Term} {t : Term} (h : ∀ x, subst τ (σ x) = υ x) :
    subst τ (subst σ t) = subst υ t := by
  induction t generalizing σ τ υ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n =>
      -- goal: subst (exts τ) (exts σ (n + 1)) = exts υ (n + 1)
      simp only [exts, ← h n]
      have e1 : subst (exts τ) (rename Nat.succ (σ n)) = subst (fun x => rename Nat.succ (τ x)) (σ n) :=
        subst_rename (fun _ => rfl)
      have e2 : rename Nat.succ (subst τ (σ n)) = subst (fun x => rename Nat.succ (τ x)) (σ n) :=
        rename_subst (fun _ => rfl)
      rw [e1, e2]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [subst, ihc h, iht h, ihe h]

theorem subst_id {σ : Nat → Term} {t : Term} (h : ∀ x, σ x = .var x) : subst σ t = t := by
  induction t generalizing σ with
  | var x => simp [subst, h]
  | lam A t ih =>
    simp only [subst]
    rw [ih]
    intro x
    cases x with
    | zero => rfl
    | succ n => simp [exts, h, rename]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | tru => rfl
  | fls => rfl
  | ite c t e ihc iht ihe => simp [subst, ihc h, iht h, ihe h]

/-- `scons v σ` maps `0` to `v` and `n + 1` to `σ n`
(written `v · σ` on paper). -/
def scons (v : Term) (σ : Nat → Term) : Nat → Term
  | 0 => v
  | n + 1 => σ n

theorem subst1_exts {v : Term} {σ : Nat → Term} {t : Term} :
    subst (subst1 v) (subst (exts σ) t) = subst (scons v σ) t := by
  apply subst_subst
  intro x
  cases x with
  | zero => rfl
  | succ n =>
    show subst (subst1 v) (rename Nat.succ (σ n)) = σ n
    have e : subst (subst1 v) (rename Nat.succ (σ n)) = subst Term.var (σ n) :=
      subst_rename (fun _ => rfl)
    rw [e, subst_id (fun _ => rfl)]

/-- `σ` is an *instantiation* of `Γ`: it maps each variable of `Γ` to a
reducible term of the right type. -/
def Inst (Γ : Ctx) (σ : Nat → Term) : Prop := ∀ x A, Γ[x]? = some A → R A (σ x)

theorem inst_cons {Γ : Ctx} {σ : Nat → Term} {A : Ty} {v : Term} :
    Inst Γ σ → R A v → Inst (A :: Γ) (scons v σ) := by
  intro hσ hv x B hx
  cases x with
  | zero =>
    simp at hx
    rw [← hx]
    exact hv
  | succ n => exact hσ n B hx

theorem fundamental {Γ : Ctx} {t : Term} {T : Ty} {σ : Nat → Term} :
    HasType Γ t T → Inst Γ σ → R T (subst σ t) := by
  intro ht hσ
  induction ht generalizing σ with
  | var h => exact hσ _ _ h
  | @lam Γ A t B _ ih =>
    -- goal: R (A ⇒ B) (subst σ (.lam A t)), which is by definition
    --       R (A ⇒ B) (.lam A (subst (exts σ) t))
    refine ⟨value_halts .lam, fun s hs => ?_⟩
    obtain ⟨v, hsv, hv⟩ := R_halts hs
    have hRv : R A v := R_star_fwd hsv hs
    have hbody : R B (subst (scons v σ) t) := ih (inst_cons hσ hRv)
    rw [← subst1_exts] at hbody
    apply R_star_back (star_app2 .lam hsv)
    exact R_back (.beta hv) hbody
  | app _ _ ihf iha => exact (ihf hσ).2 _ (iha hσ)
  | tru => exact Or.inl (.refl _)
  | fls => exact Or.inr (.refl _)
  | ite _ _ _ ihc iht ihe =>
    rcases ihc hσ with hc | hc
    · exact R_star_back (star_trans (star_ite hc) (.step .iteTrue (.refl _))) (iht hσ)
    · exact R_star_back (star_trans (star_ite hc) (.step .iteFalse (.refl _))) (ihe hσ)

/-- Executable version of `Value`. -/
def isValue : Term → Bool
  | .lam _ _ => true
  | .tru => true
  | .fls => true
  | _ => false

/-- Executable version of `Step`: `none` means "no step possible". -/
def step : Term → Option Term
  | .app f a =>
    if isValue f then
      if isValue a then
        match f with
        | .lam _ t => some (subst (subst1 a) t)
        | _ => none
      else (step a).map (.app f ·)
    else (step f).map (.app · a)
  | .ite c t e =>
    if isValue c then
      match c with
      | .tru => some t
      | .fls => some e
      | _ => none
    else (step c).map (.ite · t e)
  | _ => none

/-- Take up to `fuel` steps. -/
def eval : Nat → Term → Term
  | 0, t => t
  | n + 1, t =>
    match step t with
    | some t' => eval n t'
    | none => t

theorem isValue_complete {v : Term} : Value v → isValue v = true := by
  intro h
  cases h <;> rfl

/-- A term that steps is not a value. -/
theorem isValue_of_step {t t' : Term} : Step t t' → isValue t = false := by
  intro h
  cases h <;> rfl

/-- The interpreter can take every step of the relation. -/
theorem step_complete {t t' : Term} : Step t t' → step t = some t' := by
  intro h
  induction h with
  | beta hv => simp [step, isValue_complete hv, isValue.eq_1]
  | app1 h ih => simp [step, isValue_of_step h, ih]
  | app2 hv h ih => simp [step, isValue_complete hv, isValue_of_step h, ih]
  | iteTrue => rfl
  | iteFalse => rfl
  | ite h ih => simp [step, isValue_of_step h, ih]

/-! ## Normalization -/

/-- `λf:bool⇒bool. λx:bool. f (f x)` -/
def twiceB : Term := .lam (.bool ⇒ .bool) (.lam .bool (.app (.var 1) (.app (.var 1) (.var 0))))

/-- `λb:bool. if b then false else true` -/
def notB : Term := .lam .bool (.ite (.var 0) .fls .tru)

#eval eval 20 (.app (.app twiceB notB) .tru)

theorem normalization {t : Term} {T : Ty} : HasType [] t T → Halts t := by
  intro ht
  have h : R T (subst Term.var t) := fundamental ht (fun x A hx => by cases hx)
  rw [subst_id (fun _ => rfl)] at h
  exact R_halts h

theorem eval_of_star {t v : Term} : Star Step t v → Value v → ∃ n, eval n t = v := by
  intro hs hv
  induction hs with
  | refl => exact ⟨0, rfl⟩
  | step h _ ih =>
    obtain ⟨n, hn⟩ := ih hv
    exact ⟨n + 1, by simp [eval, step_complete h, hn]⟩

theorem eval_terminates {t : Term} {T : Ty} :
    HasType [] t T → ∃ n, Value (eval n t) := by
  intro ht
  obtain ⟨v, hs, hv⟩ := normalization ht
  obtain ⟨n, hn⟩ := eval_of_star hs hv
  exact ⟨n, hn ▸ hv⟩
