/-
# 13.08 — The interpreter agrees with the semantics

We now have two descriptions of call-by-value evaluation:

* the inductive relation `Step` — the *specification*, readable as
  inference rules, convenient for proofs;
* the function `step` — the *implementation*, which we can run.

Are they the same? In this exercise you prove the important direction,
**soundness**: every step the interpreter takes is allowed by the rules.

    step t = some t'   →   Step t t'

(and, as a warm-up, that values never step.)

## Proof strategy

Induction on `t`. The interesting case is `t = app f a`. Because `step`
matches on the *shape* of `f` and `a`, do a case analysis (`cases f`, and
for `f = lam _` also `cases a`). In each case, `simp [step] at h` computes
`step` in the hypothesis. A hypothesis like

    h : Option.map g (step a) = some t'

is simplified to `h : ∃ a', step a = some a' ∧ g a' = t'`, which you can
take apart with `obtain ⟨a', ha, rfl⟩ := h`. Then apply the matching
`Step` constructor and the induction hypothesis. Impossible cases (where
`step` returns `none`) are closed by `simp [step] at h` directly.

## Your task

Prove `value_no_step` and `step_sound`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive DTerm where
  | var (n : Nat)
  | lam (body : DTerm)
  | app (f a : DTerm)
  deriving Repr, DecidableEq, Inhabited

open DTerm

def shift (d c : Nat) : DTerm → DTerm
  | var k => if k < c then var k else var (k + d)
  | lam t => lam (shift d (c + 1) t)
  | app f a => app (shift d c f) (shift d c a)

def unshift (c : Nat) : DTerm → DTerm
  | var k => if k < c then var k else var (k - 1)
  | lam t => lam (unshift (c + 1) t)
  | app f a => app (unshift c f) (unshift c a)

def subst (j : Nat) (s : DTerm) : DTerm → DTerm
  | var k => if k = j then s else var k
  | lam t => lam (subst (j + 1) (shift 1 0 s) t)
  | app f a => app (subst j s f) (subst j s a)

def beta (t v : DTerm) : DTerm := unshift 0 (subst 0 (shift 1 0 v) t)

inductive Value : DTerm → Prop
  | lam (t : DTerm) : Value (lam t)

inductive Step : DTerm → DTerm → Prop
  | app1 {f f' a : DTerm} : Step f f' → Step (app f a) (app f' a)
  | app2 {v a a' : DTerm} : Value v → Step a a' → Step (app v a) (app v a')
  | beta {t v : DTerm} : Value v → Step (app (lam t) v) (beta t v)

def step : DTerm → Option DTerm
  | app (lam t) (lam s) => some (beta t (lam s))
  | app (lam t) a => (step a).map (fun a' => app (lam t) a')
  | app f a => (step f).map (fun f' => app f' a)
  | _ => none

/-! ## Your code -/

theorem value_no_step : ∀ v, Value v → step v = none := by
  intro v hv
  cases hv
  rfl

theorem step_sound : ∀ t t', step t = some t' → Step t t' := by
  intro t
  induction t with
  | var n => intro t' h; simp [step] at h
  | lam b _ => intro t' h; simp [step] at h
  | app f a ihf iha =>
    intro t' h
    cases f with
    | var n => simp [step] at h
    | app f1 f2 =>
      simp [step] at h
      obtain ⟨f', hf, rfl⟩ := h
      exact Step.app1 (ihf f' hf)
    | lam t =>
      cases a with
      | var n => simp [step] at h
      | lam s =>
        simp [step] at h
        subst h
        exact Step.beta (Value.lam s)
      | app a1 a2 =>
        simp [step] at h
        obtain ⟨a', ha, rfl⟩ := h
        exact Step.app2 (Value.lam t) (iha a' ha)
