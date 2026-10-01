/- HINT
`omega` closes linear arithmetic goals using the hypotheses. Constructor
equations like `n + 1 = 0` are impossible, and `contradiction` sees that.

For `from_not`: `exfalso`, then `apply hn`. For `with_have`: rewrite the
inner `f 0` with `h0`, then prove `f 1 = 2` with another `have` (or `hf 1`).
-/
example (a b : Nat) (h1 : a + 3 ≤ b) (h2 : b < 10) : a < 7 := lin a b h1 h2
example {P : Prop} (n : Nat) (h : n + 1 = 0) : P := from_false n h
example {P Q : Prop} (hp : P) (hn : ¬P) : Q := from_not hp hn
example (f : Nat → Nat) (hf : ∀ n, f n = n + 1) : f (f 0) = 2 := with_have f hf
