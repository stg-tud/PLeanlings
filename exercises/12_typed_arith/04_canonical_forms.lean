/-
# 12.04 — Canonical forms

Our goal for the rest of the chapter is **type safety**: well-typed terms
never get stuck. The proof has two halves, *progress* and *preservation*,
and both need a small but crucial lemma first.

Suppose `if c then t else e` is well-typed and `c` is a value. To make
progress we must take the `iteTrue` or `iteFalse` step, so `c` had better
be `true` or `false`, and not, say, `0`. This is what the **canonical
forms** lemma says: the values of a type have a known shape.

* If `v` is a value of type `Bool`, then `v = true` or `v = false`.
* If `v` is a value of type `Nat`, then `v` is a numeric value.

The proofs are case analyses: on the `Value` derivation, and then on the
typing derivation to rule out the mismatched combinations (`⊢ true : Nat`
fits no rule).

(In STLC there will be one more canonical forms lemma: a value of function
type `A → B` is a `λ`-abstraction. That is what makes `β`-reduction
possible in the progress proof.)

## Your task

Prove the three lemmas. `nvalue_nat` (every numeric value has type `Nat`)
goes by induction on the `NValue` derivation.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive Term where
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving Repr, DecidableEq

inductive NValue : Term → Prop
  | zero : NValue .zero
  | succ {v : Term} : NValue v → NValue (.succ v)

inductive Value : Term → Prop
  | tru : Value .tru
  | fls : Value .fls
  | nv {v : Term} : NValue v → Value v

inductive Ty where
  | bool
  | nat
  deriving Repr, DecidableEq

/-

    ─────────────── tru     ─────────────── fls     ────────────── zero
    ⊢ true : Bool           ⊢ false : Bool          ⊢ 0 : Nat

    ⊢ c : Bool    ⊢ t : T    ⊢ e : T
    ───────────────────────────────── ite
       ⊢ if c then t else e : T

      ⊢ t : Nat                ⊢ t : Nat                 ⊢ t : Nat
    ───────────────── succ   ───────────────── pred   ──────────────────── iszero
    ⊢ succ t : Nat           ⊢ pred t : Nat           ⊢ iszero t : Bool
-/
inductive HasType : Term → Ty → Prop
  | tru : HasType .tru .bool
  | fls : HasType .fls .bool
  | ite {c t e : Term} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
  | zero : HasType .zero .nat
  | succ {t : Term} : HasType t .nat → HasType (.succ t) .nat
  | pred {t : Term} : HasType t .nat → HasType (.pred t) .nat
  | iszero {t : Term} : HasType t .nat → HasType (.iszero t) .bool

/-! ## Exercises -/

theorem canonical_bool {v : Term} (hv : Value v) (ht : HasType v .bool) :
    v = .tru ∨ v = .fls := by
  sorry

theorem canonical_nat {v : Term} (hv : Value v) (ht : HasType v .nat) : NValue v := by
  sorry

theorem nvalue_nat {v : Term} (hn : NValue v) : HasType v .nat := by
  sorry
