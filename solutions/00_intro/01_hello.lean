/-
# 00.01 — Hello, Lean!

Welcome to PLeanlings! Each exercise is a small Lean file like this one.
Your job is always the same: make the file compile **without errors** and
**without any `sorry`**.

`sorry` is Lean's placeholder for "I'll fill this in later". Lean accepts a
`sorry` anywhere, but prints the warning `declaration uses 'sorry'`. The
`pleanlings` runner treats every `sorry` as "not done yet".

Keep `lake exe pleanlings` running in a terminal. It re-checks the current
exercise each time you save. Open the file in VS Code with the Lean 4
extension to see Lean's feedback live in the *infoview* panel.

Two commands are very useful while exploring:

* `#eval e` evaluates the expression `e` and shows the result.
* `#check e` shows the type of `e`.

Put your cursor on the lines below and watch the infoview.

## Your task

Replace the `sorry` in `greeting` with the string `"Hello, Lean!"`.
-/

#eval 1 + 2
#check "PLeanlings"

def greeting : String := "Hello, Lean!"

#eval greeting
