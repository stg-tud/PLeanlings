# Authoring Leanlings exercises

This guide is for people writing or maintaining exercises, not for students.

## Files

Every exercise `NN_chapter/MM_name` consists of three files:

| file | purpose |
|------|---------|
| `solutions/NN_chapter/MM_name.lean` | Reference solution. Written **first**. Must pass its checks. |
| `exercises/NN_chapter/MM_name.lean` | The solution with parts replaced by `sorry` (or a deliberate bug). What students see. |
| `checks/NN_chapter/MM_name.lean`    | Starts with a `/- HINT … -/` block, then Lean code **appended** to the student's file before compiling. |

Order is lexicographic by path. Chapters `17_…` and higher are bonus chapters.

Run `lake exe leanlings selftest NN_` to check a chapter. It verifies that:
* every solution passes its checks,
* no unsolved exercise passes, and
* the checks fit the unsolved exercise. An unsolved exercise may report "contains sorry" or "does not compile", but never "checks failed".

## Rules

* **Core Lean only.** No Mathlib, no Batteries. `import Std` is ok if really needed. Tactics available: `rfl`, `decide`, `simp`, `omega`, `cases`, `induction`, `rcases`, `obtain`, `constructor`, `exact`, `apply`, `intro`, `rw`, `unfold`, `exists`, `contradiction`, `exfalso`, `by_cases`, `split`, `injection`, `subst`, `generalize`, `revert`, `calc`, `show`, `have`, `refine`, `<;>`, `all_goals`, `repeat`, `first`, `trivial`, `left`, `right`, `fun_induction` (introduced in 11.07), `next`, `split at`, `grind`. Introduce each tactic before relying on it in an exercise.
* **Self-contained files.** Each file compiles on its own (Lean core only). Definitions from earlier exercises are restated in a section marked
  ```
  /-! ## Given (from earlier exercises) — do not edit -/
  ```
* **Small exercises.** Each file teaches one idea with 1–4 holes. A student should finish one in 2–15 minutes (proof-heavy capstone files may take longer).
* **Structure of a file:**
  ```
  /-
  # NN.MM — Title

  Explanation of the concept (short, concrete, with small code examples).
  Relate it to PL concepts where natural.

  ## Your task

  Exactly what to do.
  -/

  …code with `sorry` holes…
  ```
  Write in English, in a friendly and concise tone. Use Markdown inside comments.
* **Prefer `sorry` holes over syntax-broken code.** A hole should leave the file elaborating with only a `declaration uses sorry` warning where possible. "Fix the bug" exercises (deliberate type errors or wrong definitions) are fine occasionally.
* Avoid `#eval` on definitions that contain holes in the exercise (it is harmless, because the runner ignores "depends on sorry" errors, but it is noisy). `#eval` demos are encouraged in solutions and in exercises on fully given code.
* Do not leave a `namespace`/`section` open at the end of a file. Checks are appended at top level, so they must refer to names fully qualified (`Foo.bar`) or the file must close its namespace.
* **Checks** pin down what matters:
  * behaviour: `example : double 3 = 6 := rfl` / `by decide` / `#guard expr`
  * theorem statements, so students cannot weaken them: `example : ∀ n, double n = n + n := double_eq` (`@thm` when it has implicit arguments)
  * definitions given to the student where tampering would trivialise a proof, e.g. `example : Step (.app (.lam T t) v) … := Step.beta …`
* Hints should nudge without giving away the full solution in the first sentence. A second paragraph may get more concrete.
* Never use `axiom` in exercises (the runner rejects it; the word is fine inside comments). Do not use `native_decide`.
* Watch out for name clashes with core Lean (e.g. `not_not_intro`, `forall_and` already exist); rename or use a namespace.

## Course-wide conventions

* Relations use `inductive … : … → … → Prop`.
* Reflexive-transitive closure: `inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop | refl a : Star R a a | step : R a b → Star R b c → Star R a c`.
* STLC: de Bruijn indices; contexts `List Ty` with lookup `Γ[x]? = some T`; parallel substitution via renamings `Nat → Nat` and substitutions `Nat → Term`.
