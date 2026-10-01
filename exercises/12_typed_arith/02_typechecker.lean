/-
# 12.02 — A type checker

`HasType` *specifies* which terms are well-typed. A compiler needs an
*algorithm*: a function that computes the type of a term, or reports a
type error.

    typeOf : Term → Option Ty

For our language this is easy, because the typing rules are
**syntax-directed**: for every form of term there is exactly one rule, and
the types in the premises are determined by the subterms. So the checker
just reads the rules bottom-up. For `pred` the rule

      ⊢ t : Nat
    ────────────── pred
    ⊢ pred t : Nat

becomes

```
  | .pred t =>
    match typeOf t with
    | some .nat => some .nat      -- premise holds: the conclusion's type
    | _ => none                   -- premise fails: type error
```

For `ite` we need to check that both branches have the *same* type. Lean
can decide equality of types, `T = E`, in an `if`, because `Ty` derives
`DecidableEq`. You can match on several things at once:

```
    match typeOf c, typeOf t, typeOf e with
    | some .bool, some T, some E => …
    | _, _, _ => none
```

(In the next exercise we prove that `typeOf` agrees with `HasType`. That
proof expects exactly the shapes shown here, so stick to them.)

## Your task

Finish `typeOf`.
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

def typeOf : Term → Option Ty
  | .tru => some .bool
  | .fls => some .bool
  | .ite c t e => sorry
  | .zero => sorry
  | .succ t => sorry
  | .pred t =>
    match typeOf t with
    | some .nat => some .nat
    | _ => none
  | .iszero t => sorry
