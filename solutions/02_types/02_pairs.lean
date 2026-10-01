/-
# 02.02 — Pairs

The type `α × β` (type `\x` or `\times` for `×`) contains pairs `(a, b)`
with `a : α` and `b : β`. This is the **product type** from type theory.

    def p : Nat × String := (42, "answer")
    #eval p.1      -- 42
    #eval p.2      -- "answer"

`.1` and `.2` (also called `.fst` and `.snd`) project out the components.
Alternatively you can take a pair apart by **pattern matching**:

    def sumPair (p : Nat × Nat) : Nat :=
      match p with
      | (a, b) => a + b

or directly in a `let` or in `fun`:

    def sumPair' (p : Nat × Nat) : Nat := let (a, b) := p; a + b
    def sumPair'' : Nat × Nat → Nat := fun (a, b) => a + b

Longer tuples nest to the right: `Nat × Nat × Nat` is `Nat × (Nat × Nat)`,
so `(1, 2, 3)` is `(1, (2, 3))`.

## Your task

1. `swap p` exchanges the components of a pair.
2. `divMod n k` returns the pair (quotient, remainder) of dividing `n` by `k`.
3. `addPairs p q` adds two pairs component-wise. Use pattern matching.
-/

def swap (p : Nat × String) : String × Nat := (p.2, p.1)

def divMod (n k : Nat) : Nat × Nat := (n / k, n % k)

def addPairs (p q : Nat × Nat) : Nat × Nat :=
  match p, q with
  | (a, b), (c, d) => (a + c, b + d)

#eval swap (1, "one")
#eval divMod 17 5
#eval addPairs (1, 2) (10, 20)
