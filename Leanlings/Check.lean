import Lean.Data.Json
import Leanlings.Exercise

/-!
# Checking an exercise

The student's file and the hidden check snippet are concatenated into a
temporary file which is compiled with `lean --json`. The exercise passes when
there are no errors and no `sorry` warnings.
-/

namespace Leanlings

open Lean (Json)

structure Diagnostic where
  line : Nat
  column : Nat
  severity : String
  kind : String
  text : String
  deriving Inhabited

inductive Outcome where
  /-- Compiles, no `sorry`, checks pass. -/
  | passed
  /-- Compiles but still contains `sorry` at the given lines; `errors` lists other errors, if any. -/
  | notDone (lines : List Nat) (errors : String)
  /-- Compilation errors in the student's part of the file. -/
  | errors (output : String)
  /-- The student's file compiles, but the appended checks fail. -/
  | checkFailed (output : String)
  /-- The student introduced an `axiom` (not allowed). -/
  | usesAxiom (line : Nat)
  deriving Inhabited

def Outcome.isPassed : Outcome → Bool
  | .passed => true
  | _ => false

/-- Extract the hint from a check file: the text of a leading `/- HINT ... -/` block. -/
def readHint (e : Exercise) : IO String := do
  let p := e.checkPath
  unless ← p.pathExists do return "No hint available for this exercise."
  let content ← IO.FS.readFile p
  match content.splitOn "/- HINT" with
  | _ :: rest :: _ => return ((rest.splitOn "-/").headD "").trimAscii.toString
  | _ => return "No hint available for this exercise."

private def tmpDir : System.FilePath := ".lake" / "leanlings"

private def parseDiagnostic (s : String) : Option Diagnostic := do
  let j ← (Json.parse s).toOption
  let pos ← (j.getObjVal? "pos").toOption
  return {
    line := ((pos.getObjValAs? Nat "line").toOption).getD 0
    column := ((pos.getObjValAs? Nat "column").toOption).getD 0
    severity := ((j.getObjValAs? String "severity").toOption).getD ""
    kind := ((j.getObjValAs? String "kind").toOption).getD ""
    text := ((j.getObjValAs? String "data").toOption).getD ""
  }

private def isSorryDiag (d : Diagnostic) : Bool :=
  d.kind == "hasSorry" || ((d.text.splitOn "declaration uses").length > 1 && (d.text.splitOn "sorry").length > 1)

/-- Errors that are only a consequence of a `sorry`, e.g. `#eval` refusing to run sorried code. -/
private def isSorryConsequence (d : Diagnostic) : Bool :=
  (d.text.splitOn "depends on the 'sorry' axiom").length > 1

private def render (file : String) (ds : List Diagnostic) (maxShown : Nat := 3) : String :=
  let shown := ds.take maxShown |>.map fun d => s!"{file}:{d.line}:{d.column}: {d.severity}: {d.text}"
  let more := if ds.length > maxShown then [s!"… and {ds.length - maxShown} more error(s)."] else []
  "\n\n".intercalate (shown ++ more)

/-- Render errors in the check part, quoting the failing check line instead of its line number. -/
private def renderChecks (checkSrc : String) (offset : Nat) (ds : List Diagnostic) : String :=
  let lines := (checkSrc.splitOn "\n").toArray
  let parts := ds.take 3 |>.map fun d =>
    let src := lines.getD (d.line - offset - 1) ""
    s!"  check: {src.trimAscii}\n  {d.text.replace "\n" "\n  "}"
  "\n\n".intercalate parts

/-- Blank out comments (`-- …` and nested `/- … -/`), keeping newlines so line numbers stay valid. -/
private def stripComments (src : String) : String := Id.run do
  let cs := src.toList.toArray
  let mut out : Array Char := #[]
  let mut depth := 0
  let mut lineComment := false
  let mut inString := false
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let n := cs.getD (i + 1) ' '
    if c == '\n' then
      lineComment := false
      out := out.push c
    else if lineComment then
      out := out.push ' '
    else if depth == 0 && inString then
      if c == '\\' then out := out.push ' '; i := i + 1; out := out.push ' '
      else
        if c == '"' then inString := false
        out := out.push ' '
    else if c == '/' && n == '-' then
      depth := depth + 1; out := out.push ' ' |>.push ' '; i := i + 1
    else if depth > 0 && c == '-' && n == '/' then
      depth := depth - 1; out := out.push ' ' |>.push ' '; i := i + 1
    else if depth > 0 then
      out := out.push ' '
    else if c == '-' && n == '-' then
      lineComment := true; out := out.push ' '
    else if c == '"' then
      inString := true; out := out.push ' '
    else
      out := out.push c
    i := i + 1
  return String.ofList out.toList

/-- Find a line containing an `axiom` declaration outside comments and strings. -/
private def axiomLine? (src : String) : Option Nat :=
  ((stripComments src).splitOn "\n").zipIdx.findSome? fun (l, i) =>
    let words := l.trimAscii.toString.splitOn " "
    if words.contains "axiom" && !(words.headD "").startsWith "#" then some (i + 1) else none

/-- Compile `source` (a student file or solution) together with the exercise's checks. -/
def checkFile (e : Exercise) (source : System.FilePath) : IO Outcome := do
  let student ← IO.FS.readFile source
  if let some l := axiomLine? student then
    return .usesAxiom l
  let student := if student.endsWith "\n" then student else student ++ "\n"
  let studentLines := (student.splitOn "\n").length - 1
  let checks ← if ← e.checkPath.pathExists then IO.FS.readFile e.checkPath else pure ""
  IO.FS.createDirAll tmpDir
  let tmp := tmpDir / s!"{e.chapter}__{e.name}.lean"
  IO.FS.writeFile tmp (student ++ checks)
  let res ← IO.Process.output { cmd := "lean", args := #["--json", tmp.toString] }
  let diags := (res.stdout.splitOn "\n").filterMap parseDiagnostic
  if res.exitCode != 0 && diags.isEmpty then
    return .errors (res.stdout ++ res.stderr)
  let inStudent := diags.filter (·.line ≤ studentLines)
  let inChecks := diags.filter (·.line > studentLines)
  let sorryLines := inStudent.filter isSorryDiag |>.map (·.line)
  let studentErrors := inStudent.filter fun d => d.severity == "error" && !isSorryConsequence d
  let checkErrors := inChecks.filter (·.severity == "error")
  let file := source.toString
  if !sorryLines.isEmpty then
    return .notDone sorryLines (render file studentErrors)
  if !studentErrors.isEmpty then
    return .errors (render file studentErrors)
  if !checkErrors.isEmpty || res.exitCode != 0 then
    return .checkFailed (renderChecks checks studentLines checkErrors)
  return .passed

end Leanlings
