/-!
# Exercise discovery

Exercises live in `exercises/NN_chapter/MM_name.lean`. Every exercise has a
matching check file `checks/NN_chapter/MM_name.lean` (appended to the student's
file before compiling) and a reference solution in `solutions/`.

The order of exercises is the lexicographic order of their paths.
Chapters numbered `bonusFrom` or higher are optional bonus chapters.
-/

namespace PLeanlings

/-- Chapters with a number at least this large are bonus chapters. -/
def bonusFrom : Nat := 17

structure Exercise where
  /-- e.g. `"03_inductive"` -/
  chapter : String
  /-- e.g. `"02_lists"` -/
  name : String
  deriving BEq, Repr, Inhabited

namespace Exercise

/-- Identifier used on the command line and in the state file, e.g. `03_inductive/02_lists`. -/
def id (e : Exercise) : String := s!"{e.chapter}/{e.name}"

def relPath (e : Exercise) : System.FilePath := System.FilePath.mk e.chapter / s!"{e.name}.lean"

def exercisePath (e : Exercise) : System.FilePath := "exercises" / e.relPath
def checkPath (e : Exercise) : System.FilePath := "checks" / e.relPath
def solutionPath (e : Exercise) : System.FilePath := "solutions" / e.relPath

def chapterNumber (e : Exercise) : Nat :=
  (e.chapter.takeWhile Char.isDigit).toString.toNat!

def isBonus (e : Exercise) : Bool := e.chapterNumber ≥ bonusFrom

/-- Does `query` refer to this exercise? Accepts the full id, the file name, or the bare name. -/
def matchesQuery (e : Exercise) (query : String) : Bool :=
  let q := (query.dropSuffix ".lean").toString
  let q := (q.dropPrefix "exercises/").toString
  q == e.id || q == e.name || q == (e.name.dropWhile (fun c => c.isDigit || c == '_')).toString

end Exercise

private def sortedDir (dir : System.FilePath) : IO (Array IO.FS.DirEntry) := do
  let entries ← dir.readDir
  return entries.qsort (fun a b => a.fileName < b.fileName)

/-- All exercises, in course order. -/
def discover : IO (Array Exercise) := do
  let root : System.FilePath := "exercises"
  unless ← root.isDir do
    throw <| IO.userError "No `exercises/` directory found. Run pleanlings from the repository root."
  let mut out := #[]
  for ch in ← sortedDir root do
    unless ← ch.path.isDir do continue
    for f in ← sortedDir ch.path do
      if f.fileName.endsWith ".lean" then
        out := out.push { chapter := ch.fileName, name := (f.fileName.dropSuffix ".lean").toString }
  return out

end PLeanlings
