/-
# 10.06 — The optimizer never makes things bigger

Correctness is not the only property we expect from an optimizer: it
should also *improve* the program, or at least not make it worse. With
`size` from 10.01 as our (crude) cost measure:

    ∀ e,  (optimize e).size ≤ e.size

Again we go in two steps: a lemma about each smart constructor, then
induction. The lemmas say that a smart constructor is never bigger than
the plain node it replaces:

    (mkPlus a b).size ≤ a.size + b.size + 1

After `unfold mkPlus` and `split`, every goal is a concrete inequality
between sizes. `simp [AExp.size]` computes the sizes of the constructors
and `omega` does the arithmetic. (`split <;> simp [AExp.size] <;> omega`
runs the two on every goal; if `simp` already closes a goal, `omega` is
simply not run there.)

In the induction step, the induction hypotheses talk about
`(optimize a).size`, the lemma about `(mkPlus (optimize a) (optimize b)).size`.
Put the lemma instance into the context with
`have h := size_mkPlus (optimize a) (optimize b)`, unfold, and let `omega`
combine everything.

## Your task

Prove `size_mkPlus`, `size_mkTimes` and `size_optimize`.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive AExp where
  | num   (n : Nat)
  | var   (x : String)
  | plus  (a b : AExp)
  | times (a b : AExp)
  deriving Repr, DecidableEq

def AExp.size : AExp → Nat
  | .num _ => 1
  | .var _ => 1
  | .plus a b => a.size + b.size + 1
  | .times a b => a.size + b.size + 1

def mkPlus : AExp → AExp → AExp
  | .num n, .num m => .num (n + m)
  | .num 0, b => b
  | a, .num 0 => a
  | a, b => .plus a b

def mkTimes : AExp → AExp → AExp
  | .num n, .num m => .num (n * m)
  | .num 0, _ => .num 0
  | _, .num 0 => .num 0
  | .num 1, b => b
  | a, .num 1 => a
  | a, b => .times a b

def optimize : AExp → AExp
  | .num n => .num n
  | .var x => .var x
  | .plus a b => mkPlus (optimize a) (optimize b)
  | .times a b => mkTimes (optimize a) (optimize b)

/-! ## Exercises -/

theorem size_mkPlus (a b : AExp) : (mkPlus a b).size ≤ a.size + b.size + 1 := by
  sorry

theorem size_mkTimes (a b : AExp) : (mkTimes a b).size ≤ a.size + b.size + 1 := by
  sorry

theorem size_optimize (e : AExp) : (optimize e).size ≤ e.size := by
  induction e with
  | num n => simp [optimize]
  | var x => simp [optimize]
  | plus a b iha ihb =>
    sorry
  | times a b iha ihb =>
    sorry
