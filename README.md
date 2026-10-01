# Leanlings 🦉

Small exercises to get you used to reading and writing [Lean 4](https://lean-lang.org/),
from your first `#eval` to a **verified implementation of the simply typed lambda calculus**.
The course is inspired by [rustlings](https://github.com/rust-lang/rustlings) and [ziglings](https://codeberg.org/ziglings/exercises).

Leanlings is aimed at students of programming languages. By the end you will have

* written ASTs and interpreters for small languages,
* defined operational semantics and type systems as inductive relations,
* worked with the untyped lambda calculus, variable capture and de Bruijn indices,
* implemented the simply typed lambda calculus (STLC) with a type checker and an evaluator, and
* **proven** progress, preservation, type safety, uniqueness of types, and the soundness and completeness of your type checker.

You do not need to write a parser: programs are written directly as abstract syntax trees.

## Setup

1. Install Lean with [elan](https://github.com/leanprover/elan):
   ```sh
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```
2. Install [VS Code](https://code.visualstudio.com/) and the **Lean 4** extension. Other editors with Lean support (Emacs, Neovim) work too.
3. Clone this repository and start Leanlings:
   ```sh
   git clone <this repo> leanlings && cd leanlings
   lake exe leanlings
   ```
   The first start downloads the right Lean version and builds the runner, which takes a minute.

## How it works

Leanlings runs in *watch mode*. It shows you the current exercise and re-checks it every time you save the file:

```
Leanlings — progress: [#####...................................] 9/80
Current exercise: exercises/03_inductive/02_lists.lean

✗ exercises/03_inductive/02_lists.lean still contains `sorry` (line 21).
  Replace every `sorry` with a real definition or proof.

Commands (type + Enter):  h = hint   l = list   r = re-check   q = quit
```

Open the exercise in your editor and read the explanation at the top. Then replace every `sorry` with a definition or a proof.
An exercise is done when the file compiles **without errors and without `sorry`**, and the hidden checks pass.
Leanlings then moves on to the next exercise automatically.

Keep the Lean *infoview* open in VS Code (`Ctrl+Shift+Enter`). It shows the results of `#eval`, the types from `#check`, and, most importantly, the current proof goal.

### Commands

| command | |
|---|---|
| `lake exe leanlings` | watch mode (start here) |
| `lake exe leanlings list` | all exercises and your progress |
| `lake exe leanlings hint [name]` | a hint for the current (or the named) exercise |
| `lake exe leanlings run [name]` | check a single exercise once |
| `lake exe leanlings verify` | check all exercises in order |
| `lake exe leanlings reset <name>` | restore an exercise to its original state |

Your progress is stored in `.leanlings-state`.

### Rules of the game

* Do not edit the sections marked **"Given — do not edit"**, and do not change theorem statements.
  Hidden checks are appended to your file and will notice. Weakening a theorem would be no fun anyway.
* `axiom` is not allowed (it can prove anything).
* You may add your own helper definitions and lemmas whenever you like.

## Contents

| part | chapter | topics |
|---|---|---|
| **I. Programming in Lean** | 00 intro | `#eval`, `#check`, `sorry`, error messages |
| | 01 functions | definitions, lambdas, currying, higher-order functions |
| | 02 types | basic types, products, structures, `Option` |
| | 03 inductive | inductive types, pattern matching, structural recursion |
| | 04 polymorphism | generics, map/filter/fold, type classes |
| | 05 monads | `Option`, `Except`, `do` notation |
| **II. Proving in Lean** | 06 props | propositions as types (Curry–Howard) |
| | 07 tactics | `intro`, `apply`, `rw`, `simp`, `cases`, `omega`, … |
| | 08 induction | induction on numbers and lists, generalizing |
| | 09 relations | inductive predicates, inference rules, rule induction |
| **III. Programming languages** | 10 arith | ASTs, interpreters, a verified optimizer |
| | 11 semantics | small-step and big-step operational semantics |
| | 12 typed arith | type systems, type checkers, progress & preservation |
| | 13 untyped lambda | λ-calculus, capture, de Bruijn indices, Church encodings |
| | 14 stlc | the simply typed λ-calculus: typing, substitution, evaluation |
| | 15 stlc metatheory | weakening, substitution lemma, type safety, type checker correctness |
| | 16 capstone | put it all together |
| **Bonus** | 17 stlc extensions | `let`, pairs, sums, `fix` |
| | 18 normalization | termination of well-typed programs via logical relations (Tait) |

## For instructors and contributors

See [AUTHORING.md](AUTHORING.md). Reference solutions are in `solutions/`.
`lake exe leanlings selftest` checks that all solutions pass and that no unsolved exercise passes.

## Further reading

* Benjamin C. Pierce, *Types and Programming Languages* (TAPL)
* *Programming Language Foundations in Agda* (PLFA), https://plfa.github.io
* *Software Foundations*, Vol. 1–2, https://softwarefoundations.cis.upenn.edu
* *Theorem Proving in Lean 4* and *Functional Programming in Lean*, https://lean-lang.org/documentation
