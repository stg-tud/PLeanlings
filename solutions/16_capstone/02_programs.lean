/-
# 16.02 — Capstone: running well-typed programs

This file is the **complete** STLC development of chapters 14–16 in one place:
definitions, interpreter, type checker, and all the proofs. Read through
the Given section and enjoy how the pieces fit together.

As a last exercise, write a few STLC programs yourself. Let the type checker
confirm that they are well-typed (`decide` runs `typeOf` through the
`Decidable` instance from 15.09), and run them with the interpreter. Type safety
then tells us that running them can never get stuck. Note the final example
of this file: it *applies* `type_safety` to a concrete program.

## Your task

1. `compose A B C`: `λf:B⇒C. λg:A⇒B. λx:A. f (g x)`, and prove it has type
   `(B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C` for *all* types `A B C`. `decide` cannot do
   this, because `A`, `B`, `C` are variables, so build the derivation by hand.
2. `isOne : Term` of type `nat ⇒ bool`, returning `true` exactly for `1`.
   (Hint: `pred` and `iszero`.) Prove its typing with `decide`.
3. `andFn : Term` of type `bool ⇒ bool ⇒ bool`, the boolean conjunction.
-/

/-! ## Given (from earlier exercises) — do not edit -/

/-- Reflexive-transitive closure of a relation. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl a : Star R a a
  | step : R a b → Star R b c → Star R a c

/-- Types: `T ::= bool | nat | T ⇒ T`. -/
inductive Ty where
  | bool
  | nat
  | arrow (A B : Ty)
  deriving DecidableEq

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
  deriving DecidableEq

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

/-- Executable version of `Value`. -/
def isValue : Term → Bool
  | .lam _ _ => true
  | .tru => true
  | .fls => true
  | .zero => true
  | .succ t => isValue t
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
  | .succ t => (step t).map .succ
  | .pred t =>
    if isValue t then
      match t with
      | .zero => some .zero
      | .succ v => some v
      | _ => none
    else (step t).map .pred
  | .iszero t =>
    if isValue t then
      match t with
      | .zero => some .tru
      | .succ _ => some .fls
      | _ => none
    else (step t).map .iszero
  | _ => none

/-- Take up to `fuel` steps. -/
def eval : Nat → Term → Term
  | 0, t => t
  | n + 1, t =>
    match step t with
    | some t' => eval n t'
    | none => t

/-- Pretty printing. Variables are named after the depth of their binder,
so `lam .nat (lam .nat (var 1))` prints as `(λx0 : nat. (λx1 : nat. x0))`. -/
def Ty.pretty : Ty → String
  | .bool => "bool"
  | .nat => "nat"
  | .arrow (.arrow A B) C => s!"({(Ty.arrow A B).pretty}) ⇒ {C.pretty}"
  | .arrow A B => s!"{A.pretty} ⇒ {B.pretty}"

def Term.toNat? : Term → Option Nat
  | .zero => some 0
  | .succ t => t.toNat?.map (· + 1)
  | _ => none

def Term.pretty (depth : Nat) : Term → String
  | .var x => if x < depth then s!"x{depth - 1 - x}" else s!"#{x}"
  | .lam A t => s!"(λx{depth} : {A.pretty}. {t.pretty (depth + 1)})"
  | .app f a => s!"({f.pretty depth} {a.pretty depth})"
  | .tru => "true"
  | .fls => "false"
  | .ite c t e => s!"(if {c.pretty depth} then {t.pretty depth} else {e.pretty depth})"
  | .zero => "0"
  | .succ t =>
    match t.toNat? with
    | some n => toString (n + 1)
    | none => s!"(succ {t.pretty depth})"
  | .pred t => s!"(pred {t.pretty depth})"
  | .iszero t => s!"(iszero {t.pretty depth})"

instance : Repr Ty where
  reprPrec T p := match T with
    | .arrow _ _ => Repr.addAppParen T.pretty p
    | _ => T.pretty
instance : Repr Term := ⟨fun t _ => t.pretty 0⟩

/-- The numeral `n` as a term: `succ (succ … zero)`. -/
def Term.num : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (Term.num n)

/-! ### Metatheory -/

theorem canonical_bool {Γ : Ctx} {v : Term} :
    HasType Γ v .bool → Value v → v = .tru ∨ v = .fls := by
  intro ht hv
  cases hv with
  | tru => exact Or.inl rfl
  | fls => exact Or.inr rfl
  | _ => cases ht

theorem canonical_nat {Γ : Ctx} {v : Term} :
    HasType Γ v .nat → Value v → v = .zero ∨ ∃ n, v = .succ n ∧ Value n := by
  intro ht hv
  cases hv with
  | zero => exact Or.inl rfl
  | succ hn => exact Or.inr ⟨_, rfl, hn⟩
  | _ => cases ht

theorem canonical_arrow {Γ : Ctx} {v : Term} {A B : Ty} :
    HasType Γ v (A ⇒ B) → Value v → ∃ t, v = .lam A t := by
  intro ht hv
  cases hv with
  | lam =>
    cases ht
    exact ⟨_, rfl⟩
  | _ => cases ht

theorem progress {t : Term} {T : Ty} :
    HasType [] t T → Value t ∨ ∃ t', Step t t' := by
  intro ht
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var h =>
    subst hΓ
    cases h
  | lam _ _ => exact Or.inl .lam
  | app hf ha ihf iha =>
    subst hΓ
    rcases ihf rfl with hvf | ⟨f', hf'⟩
    · rcases iha rfl with hva | ⟨a', ha'⟩
      · obtain ⟨t, rfl⟩ := canonical_arrow hf hvf
        exact Or.inr ⟨_, .beta hva⟩
      · exact Or.inr ⟨_, .app2 hvf ha'⟩
    · exact Or.inr ⟨_, .app1 hf'⟩
  | tru => exact Or.inl .tru
  | fls => exact Or.inl .fls
  | ite hc _ _ ihc _ _ =>
    subst hΓ
    rcases ihc rfl with hvc | ⟨c', hc'⟩
    · rcases canonical_bool hc hvc with rfl | rfl
      · exact Or.inr ⟨_, .iteTrue⟩
      · exact Or.inr ⟨_, .iteFalse⟩
    · exact Or.inr ⟨_, .ite hc'⟩
  | zero => exact Or.inl .zero
  | succ _ ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · exact Or.inl (.succ hv)
    · exact Or.inr ⟨_, .succ ht'⟩
  | pred h ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · rcases canonical_nat h hv with rfl | ⟨n, rfl, hn⟩
      · exact Or.inr ⟨_, .predZero⟩
      · exact Or.inr ⟨_, .predSucc hn⟩
    · exact Or.inr ⟨_, .pred ht'⟩
  | iszero h ih =>
    subst hΓ
    rcases ih rfl with hv | ⟨t', ht'⟩
    · rcases canonical_nat h hv with rfl | ⟨n, rfl, hn⟩
      · exact Or.inr ⟨_, .iszeroZero⟩
      · exact Or.inr ⟨_, .iszeroSucc hn⟩
    · exact Or.inr ⟨_, .iszero ht'⟩

theorem ext_ok {Γ Δ : Ctx} {ρ : Nat → Nat} {B : Ty}
    (hρ : ∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) :
    ∀ x A, (B :: Γ)[x]? = some A → (B :: Δ)[ext ρ x]? = some A := by
  intro x A hx
  cases x with
  | zero => exact hx
  | succ n => exact hρ n A hx

theorem rename_typing {Γ Δ : Ctx} {ρ : Nat → Nat} {t : Term} {T : Ty}
    (hρ : ∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A) :
    HasType Γ t T → HasType Δ (rename ρ t) T := by
  intro ht
  induction ht generalizing Δ ρ with
  | var h => exact .var (hρ _ _ h)
  | lam _ ih => exact .lam (ih (ext_ok hρ))
  | app _ _ ihf iha => exact .app (ihf hρ) (iha hρ)
  | tru => exact .tru
  | fls => exact .fls
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hρ) (iht hρ) (ihe hρ)
  | zero => exact .zero
  | succ _ ih => exact .succ (ih hρ)
  | pred _ ih => exact .pred (ih hρ)
  | iszero _ ih => exact .iszero (ih hρ)

theorem weakening {Γ : Ctx} {t : Term} {T B : Ty} :
    HasType Γ t T → HasType (B :: Γ) (rename Nat.succ t) T :=
  rename_typing (fun _ _ h => h)

theorem exts_ok {Γ Δ : Ctx} {σ : Nat → Term} {B : Ty}
    (hσ : ∀ x A, Γ[x]? = some A → HasType Δ (σ x) A) :
    ∀ x A, (B :: Γ)[x]? = some A → HasType (B :: Δ) (exts σ x) A := by
  intro x A hx
  cases x with
  | zero => exact .var hx
  | succ n => exact weakening (hσ n A hx)

theorem subst_typing {Γ Δ : Ctx} {σ : Nat → Term} {t : Term} {T : Ty}
    (hσ : ∀ x A, Γ[x]? = some A → HasType Δ (σ x) A) :
    HasType Γ t T → HasType Δ (subst σ t) T := by
  intro ht
  induction ht generalizing Δ σ with
  | var h => exact hσ _ _ h
  | lam _ ih => exact .lam (ih (exts_ok hσ))
  | app _ _ ihf iha => exact .app (ihf hσ) (iha hσ)
  | tru => exact .tru
  | fls => exact .fls
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hσ) (iht hσ) (ihe hσ)
  | zero => exact .zero
  | succ _ ih => exact .succ (ih hσ)
  | pred _ ih => exact .pred (ih hσ)
  | iszero _ ih => exact .iszero (ih hσ)

theorem subst1_ok {Γ : Ctx} {s : Term} {A : Ty} (hs : HasType Γ s A) :
    ∀ x B, (A :: Γ)[x]? = some B → HasType Γ (subst1 s x) B := by
  intro x B hx
  cases x with
  | zero =>
    simp at hx
    rw [← hx]
    exact hs
  | succ n => exact .var hx

theorem subst1_typing {Γ : Ctx} {s t : Term} {A B : Ty} :
    HasType (A :: Γ) t B → HasType Γ s A → HasType Γ (subst (subst1 s) t) B :=
  fun ht hs => subst_typing (subst1_ok hs) ht

theorem preservation {Γ : Ctx} {t t' : Term} {T : Ty} :
    HasType Γ t T → Step t t' → HasType Γ t' T := by
  intro ht hs
  induction ht generalizing t' with
  | var _ => cases hs
  | lam _ _ => cases hs
  | app hf ha ihf iha =>
    cases hs with
    | beta _ =>
      cases hf with
      | lam hbody => exact subst1_typing hbody ha
    | app1 hs' => exact .app (ihf hs') ha
    | app2 _ hs' => exact .app hf (iha hs')
  | tru => cases hs
  | fls => cases hs
  | ite hc ht he ihc _ _ =>
    cases hs with
    | iteTrue => exact ht
    | iteFalse => exact he
    | ite hs' => exact .ite (ihc hs') ht he
  | zero => cases hs
  | succ _ ih =>
    cases hs with
    | succ hs' => exact .succ (ih hs')
  | pred h ih =>
    cases hs with
    | predZero => exact .zero
    | predSucc _ =>
      cases h with
      | succ h' => exact h'
    | pred hs' => exact .pred (ih hs')
  | iszero _ ih =>
    cases hs with
    | iszeroZero => exact .tru
    | iszeroSucc _ => exact .fls
    | iszero hs' => exact .iszero (ih hs')

theorem preservation_star {Γ : Ctx} {t t' : Term} {T : Ty} :
    HasType Γ t T → Star Step t t' → HasType Γ t' T := by
  intro ht hs
  induction hs with
  | refl => exact ht
  | step h₁ _ ih => exact ih (preservation ht h₁)

theorem type_safety {t t' : Term} {T : Ty} :
    HasType [] t T → Star Step t t' → Value t' ∨ ∃ t'', Step t' t'' := by
  intro ht hs
  exact progress (preservation_star ht hs)

theorem type_unique {Γ : Ctx} {t : Term} {A B : Ty} :
    HasType Γ t A → HasType Γ t B → A = B := by
  intro h1 h2
  induction h1 generalizing B with
  | var h =>
    cases h2 with
    | var h' =>
      rw [h] at h'
      injection h'
  | lam _ ih =>
    cases h2 with
    | lam h' => rw [ih h']
  | app _ _ ihf _ =>
    cases h2 with
    | app hf' _ =>
      have h := ihf hf'
      injection h
  | tru => cases h2; rfl
  | fls => cases h2; rfl
  | ite _ _ _ _ iht _ =>
    cases h2 with
    | ite _ ht' _ => exact iht ht'
  | zero => cases h2; rfl
  | succ _ _ => cases h2; rfl
  | pred _ _ => cases h2; rfl
  | iszero _ _ => cases h2; rfl

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

theorem typeOf_complete {Γ : Ctx} {t : Term} {T : Ty} :
    HasType Γ t T → typeOf Γ t = some T := by
  intro h
  induction h with
  | var h => exact h
  | lam _ ih => simp [typeOf, ih]
  | app _ _ ihf iha => simp [typeOf, ihf, iha]
  | tru => rfl
  | fls => rfl
  | ite _ _ _ ihc iht ihe => simp [typeOf, ihc, iht, ihe]
  | zero => rfl
  | succ _ ih => simp [typeOf, ih]
  | pred _ ih => simp [typeOf, ih]
  | iszero _ ih => simp [typeOf, ih]

theorem hasType_iff {Γ : Ctx} {t : Term} {T : Ty} :
    HasType Γ t T ↔ typeOf Γ t = some T :=
  ⟨typeOf_complete, typeOf_sound⟩

/-- Typing is decidable: ask the type checker. Now `decide` proves typing goals. -/
instance (Γ : Ctx) (t : Term) (T : Ty) : Decidable (HasType Γ t T) :=
  decidable_of_iff (typeOf Γ t = some T) hasType_iff.symm

theorem isValue_sound {t : Term} : isValue t = true → Value t := by
  intro h
  induction t with
  | lam => exact .lam
  | tru => exact .tru
  | fls => exact .fls
  | zero => exact .zero
  | succ t ih => exact .succ (ih h)
  | _ => simp [isValue] at h

theorem step_sound {t t' : Term} : step t = some t' → Step t t' := by
  induction t generalizing t' with
  | app f a ihf iha =>
    intro h
    simp only [step] at h
    split at h
    · next hf =>
      split at h
      · next ha =>
        split at h
        · injection h with h
          rw [← h]
          exact .beta (isValue_sound ha)
        · contradiction
      · cases hs : step a with
        | none => simp [hs] at h
        | some a' =>
          simp [hs] at h
          rw [← h]
          exact .app2 (isValue_sound hf) (iha hs)
    · cases hs : step f with
      | none => simp [hs] at h
      | some f' =>
        simp [hs] at h
        rw [← h]
        exact .app1 (ihf hs)
  | ite c t e ihc =>
    intro h
    simp only [step] at h
    split at h
    · split at h
      · injection h with h
        rw [← h]
        exact .iteTrue
      · injection h with h
        rw [← h]
        exact .iteFalse
      · contradiction
    · cases hs : step c with
      | none => simp [hs] at h
      | some c' =>
        simp [hs] at h
        rw [← h]
        exact .ite (ihc hs)
  | succ t ih =>
    intro h
    simp only [step] at h
    cases hs : step t with
    | none => simp [hs] at h
    | some t'' =>
      simp [hs] at h
      rw [← h]
      exact .succ (ih hs)
  | pred t ih =>
    intro h
    simp only [step] at h
    split at h
    · next hv =>
      split at h
      · injection h with h
        rw [← h]
        exact .predZero
      · injection h with h
        rw [← h]
        exact .predSucc (isValue_sound hv)
      · contradiction
    · cases hs : step t with
      | none => simp [hs] at h
      | some t'' =>
        simp [hs] at h
        rw [← h]
        exact .pred (ih hs)
  | iszero t ih =>
    intro h
    simp only [step] at h
    split at h
    · next hv =>
      split at h
      · injection h with h
        rw [← h]
        exact .iszeroZero
      · injection h with h
        rw [← h]
        exact .iszeroSucc (isValue_sound hv)
      · contradiction
    · cases hs : step t with
      | none => simp [hs] at h
      | some t'' =>
        simp [hs] at h
        rw [← h]
        exact .iszero (ih hs)
  | _ =>
    intro h
    simp [step] at h

theorem eval_star (n : Nat) (t : Term) : Star Step t (eval n t) := by
  induction n generalizing t with
  | zero => exact .refl t
  | succ n ih =>
    simp only [eval]
    cases h : step t with
    | none => exact .refl t
    | some t' => exact .step (step_sound h) (ih t')

/-! ### Example programs -/

/-- `λx:nat. succ x` -/
def succFn : Term := .lam .nat (.succ (.var 0))

/-- `λb:bool. if b then false else true` -/
def notFn : Term := .lam .bool (.ite (.var 0) .fls .tru)

/-- `λf:A⇒A. λx:A. f (f x)`, one copy for every type `A`. -/
def twice (A : Ty) : Term := .lam (A ⇒ A) (.lam A (.app (.var 1) (.app (.var 1) (.var 0))))

#eval eval 100 (.app (.app (.app (twice (.nat ⇒ .nat)) (twice .nat)) succFn) .zero)
#eval typeOf [] (twice (.nat ⇒ .nat))

/-! ## Your programs -/

def compose (A B C : Ty) : Term :=
  .lam (B ⇒ C) (.lam (A ⇒ B) (.lam A (.app (.var 2) (.app (.var 1) (.var 0)))))

theorem compose_typed (A B C : Ty) :
    HasType [] (compose A B C) ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) :=
  .lam (.lam (.lam (.app (.var rfl) (.app (.var rfl) (.var rfl)))))

def isOne : Term := .lam .nat (.ite (.iszero (.var 0)) .fls (.iszero (.pred (.var 0))))

theorem isOne_typed : HasType [] isOne (.nat ⇒ .bool) := by decide

def andFn : Term := .lam .bool (.lam .bool (.ite (.var 1) (.var 0) .fls))

#eval eval 100 (.app isOne (Term.num 1))
#eval eval 100 (.app (.app (.app (compose .nat .nat .bool) isOne) succFn) .zero)
#eval eval 100 (.app (.app andFn .tru) (.app isOne (Term.num 3)))

/-- Type safety in action: whatever `isOne 7` reduces to is never stuck. -/
example : ∀ t', Star Step (.app isOne (Term.num 7)) t' → Value t' ∨ ∃ t'', Step t' t'' :=
  fun _ hs => type_safety (.app isOne_typed (typeOf_sound rfl)) hs

/-
# Congratulations!

You have implemented the simply typed lambda calculus in Lean and proven its
central metatheorems:

* **progress** and **preservation**, and hence **type safety**,
* **uniqueness of types**,
* **soundness and completeness** of a type checker, so typing is **decidable**,
* **soundness** of an interpreter with respect to the small-step semantics.

All of it is machine-checked, and every step follows the pen-and-paper proofs in
TAPL. Along the way you met the standard tools of mechanised
metatheory: de Bruijn indices, parallel substitution, induction on
derivations, and inversion.

## Where to go next

* **Bonus chapter 17** extends STLC with `let`, pairs, sums and `fix`.
  Every new construct means new cases in the proofs you just wrote, and `fix`
  brings back non-termination.
* **Bonus chapter 18** proves that every well-typed STLC program terminates
  (*normalization*). The naive induction fails, so you need a **logical relation**
  (Tait's method), which is one of the most important proof techniques in PL theory.

Further reading:

* Benjamin C. Pierce, *Types and Programming Languages* (TAPL), chapters 8–12.
* Wadler, Kokke, Siek, *Programming Language Foundations in Agda* (PLFA),
  free online, whose substitution design we followed.
* Pierce et al., *Software Foundations*, volume 2 (*Programming Language
  Foundations*), which covers the same ground in Coq/Rocq.
-/
