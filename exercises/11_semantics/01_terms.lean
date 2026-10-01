/-
# 11.01 — Booleans and numbers: terms and values

In this chapter we study the small language from chapter 3 of Pierce's
*Types and Programming Languages* (TAPL). Its grammar is

    t ::= true | false | if t then t else t
        | 0 | succ t | pred t | iszero t

Numbers are written in *unary*: `2` is `succ (succ 0)`. As a Lean type:

```
inductive Term where
  | tru                          -- true
  | fls                          -- false
  | ite (c t e : Term)           -- if c then t else e
  | zero                         -- 0
  | succ (t : Term)              -- succ t
  | pred (t : Term)              -- pred t
  | iszero (t : Term)            -- iszero t
```

(`true`/`false`/`if` are taken by Lean, hence `tru`, `fls`, `ite`.)

Some terms are *finished computing*: these are the **values**, the
possible results of a program. A value is a boolean or a **numeric value**
`succ (succ … (succ 0))`. We define them as inductive predicates, i.e. by
inference rules:

                         NValue v
    ──────── zero     ─────────────── succ
    NValue 0          NValue (succ v)

    ─────────── tru   ─────────── fls       NValue v
    Value true        Value false        ───────────── nv
                                            Value v

Note that `succ true` and `pred 0` are terms, but not values: `pred 0`
still has to compute, and `succ true` is nonsense, as we will see.

## Your task

1. Define `Term.ofNat`, which turns a Lean number into a numeric term
   (`ofNat 2 = succ (succ zero)`), and prove that its result is always an
   `NValue`.
2. Prove that `succ (succ 0)` is a value.
3. Prove that `succ true` is *not* a value. (Use `cases` on the
   hypothesis `Value (succ tru)`: which rules could have derived it?)
-/

/-! ## Given — do not edit -/

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

/-! ## Exercises -/

def Term.ofNat : Nat → Term
  | 0 => sorry
  | n + 1 => sorry

theorem nvalue_ofNat (n : Nat) : NValue (Term.ofNat n) := by
  sorry

theorem value_two : Value (.succ (.succ .zero)) :=
  sorry

theorem succ_tru_not_value : ¬ Value (.succ .tru) := by
  sorry
