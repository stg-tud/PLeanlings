import PLeanlings.Check
import PLeanlings.State

namespace PLeanlings

def green (s : String) : String := s!"\x1b[32m{s}\x1b[0m"
def red (s : String) : String := s!"\x1b[31m{s}\x1b[0m"
def yellow (s : String) : String := s!"\x1b[33m{s}\x1b[0m"
def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
def dim (s : String) : String := s!"\x1b[2m{s}\x1b[0m"

def clearScreen : IO Unit := IO.print "\x1b[2J\x1b[H"

def progressBar (done total : Nat) (width : Nat := 40) : String :=
  let filled := if total == 0 then 0 else done * width / total
  "[" ++ "".pushn '#' filled ++ "".pushn '.' (width - filled) ++ s!"] {done}/{total}"

def printProgress (exs : Array Exercise) (done : List String) : IO Unit := do
  let core := exs.filter (!·.isBonus)
  let bonus := exs.filter (·.isBonus)
  let coreDone := core.filter (done.contains ·.id) |>.size
  IO.println s!"{bold "PLeanlings"} — progress: {progressBar coreDone core.size}"
  if bonus.size > 0 then
    let bonusDone := bonus.filter (done.contains ·.id) |>.size
    IO.println (dim s!"           bonus:    {progressBar bonusDone bonus.size}")

def printOutcome (e : Exercise) (o : Outcome) (path : System.FilePath := e.exercisePath) : IO Unit := do
  match o with
  | .passed =>
    IO.println (green s!"✓ {e.id} passed!")
  | .notDone lines errs =>
    let ls := ", ".intercalate (lines.eraseDups.map toString)
    IO.println (yellow s!"✗ {path} still contains `sorry` (line {ls}).")
    IO.println "  Replace every `sorry` with a real definition or proof."
    unless errs.isEmpty do
      IO.println ""
      IO.println (red "Errors:")
      IO.println errs
  | .errors out =>
    IO.println (red s!"✗ {path} does not compile:")
    IO.println ""
    IO.println out
  | .checkFailed out =>
    IO.println (red s!"✗ {path} compiles, but the checks failed.")
    IO.println "  Did you change a definition or theorem statement? The checks expect:"
    IO.println ""
    IO.println out
  | .usesAxiom l =>
    IO.println (red s!"✗ {path}:{l}: `axiom` is not allowed — that would let you prove anything!")

/-- List all exercises with their status. -/
def printList (exs : Array Exercise) (done : List String) (current : Option Exercise) : IO Unit := do
  let mut lastChapter := ""
  for e in exs do
    if e.chapter != lastChapter then
      lastChapter := e.chapter
      IO.println ""
      IO.println (bold (e.chapter ++ if e.isBonus then "  (bonus)" else ""))
    let mark := if done.contains e.id then green "✓" else if current == some e then yellow "→" else " "
    IO.println s!"  {mark} {e.name}"

end PLeanlings
