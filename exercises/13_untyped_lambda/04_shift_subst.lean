/-
# 13.04 — Shifting and substitution with de Bruijn indices

With de Bruijn indices capture cannot happen — but we pay in another
currency: when a term is moved **under a binder**, its free variables must
be renumbered, because there is now one more `λ` between them and their
binders.

Example: substitute `s = 0` (a free variable, "the nearest outer binder")
into the body of `λ. 1`. Inside the `λ`, that same outer variable is
called `1`, not `0`! So `s` must be **shifted** to `1` first.

## Shifting (TAPL §6.2)

`shift d c t` (written `↑ᵈ_c t`) adds `d` to every *free* index of `t`
that is `≥ c`. The **cutoff** `c` counts the binders we have gone under
inside `t` itself: indices below `c` are bound inside `t` and must not
move.

    ↑ᵈ_c (k)      = k              if k < c
                  = k + d          if k ≥ c
    ↑ᵈ_c (λ. t)   = λ. ↑ᵈ_(c+1) t
    ↑ᵈ_c (t₁ t₂)  = (↑ᵈ_c t₁) (↑ᵈ_c t₂)

For example `↑¹₀ (λ. 0 1) = λ. 0 2`: the `0` is bound by the `λ`, the `1`
is free and gets shifted.

## Substitution

`subst j s t` (written `[j ↦ s] t`) replaces variable `j` by `s`. Going
under a binder, the variable we are looking for is now called `j + 1`, and
`s` must be shifted by one, as explained above:

    [j ↦ s] k        = s              if k = j
                     = k              otherwise
    [j ↦ s] (λ. t)   = λ. [j+1 ↦ ↑¹₀ s] t
    [j ↦ s] (t₁ t₂)  = ([j ↦ s] t₁) ([j ↦ s] t₂)

## β-reduction

`(λ. t) v` should replace index `0` of `t` by `v`. Afterwards the binder
is gone, so all other free indices of `t` must go **down** by one. To
avoid `v`'s own free variables being lowered too, TAPL shifts `v` up first:

    (λ. t) v   ⟶   ↓( [0 ↦ ↑¹₀ v] t )

Here `↓` is `unshift 0`, given below (it subtracts one from free indices;
it is only applied when index `0` no longer occurs).

> **Outlook.** In the STLC chapters we will use a slicker technique,
> *parallel substitution* with renamings `Nat → Nat` and substitutions
> `Nat → Term` (as in PLFA). It replaces `shift`, `subst` and `unshift` by
> a single operation, which makes the proofs much easier. The idea —
> adjust indices whenever you cross a binder — is the same.

## Your task

Implement `shift` and `subst`. `unshift` is given and has exactly the shape
`shift` should have.
-/

/-! ## Given (from earlier exercises) — do not edit -/

inductive DTerm where
  | var (n : Nat)
  | lam (body : DTerm)
  | app (f a : DTerm)
  deriving Repr, DecidableEq, Inhabited

open DTerm

/-- `unshift c t` lowers every free index `≥ c` by one. -/
def unshift (c : Nat) : DTerm → DTerm
  | var k => if k < c then var k else var (k - 1)
  | lam t => lam (unshift (c + 1) t)
  | app f a => app (unshift c f) (unshift c a)

/-! ## Your code -/

/-- `shift d c t`: add `d` to every free index `≥ c`. -/
def shift (d c : Nat) : DTerm → DTerm
  | var k => sorry
  | lam t => sorry
  | app f a => sorry

/-- `subst j s t`: replace variable `j` by `s` in `t`. -/
def subst (j : Nat) (s : DTerm) : DTerm → DTerm
  | var k => sorry
  | lam t => sorry
  | app f a => sorry

/-! ## Given — do not edit -/

/-- The result of β-reducing `(λ. t) v`. -/
def beta (t v : DTerm) : DTerm := unshift 0 (subst 0 (shift 1 0 v) t)

-- Once you are done: (λx. λy. x) (λz. z)  ⟶  λy. λz. z
-- #eval beta (lam (var 1)) (lam (var 0))
