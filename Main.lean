import Leanlings

open Leanlings

def usage : String := "Usage: lake exe leanlings [command]

Commands:
  watch            (default) check the current exercise whenever you save it
  list             show all exercises and your progress
  hint [name]      show a hint for an exercise (default: the current one)
  run <name>       check a single exercise
  verify           check all exercises in order, stop at the first unfinished one
  reset <name>     restore an exercise to its original state (uses git)

Maintainer commands:
  verify --solutions   check every reference solution against its checks
  selftest [prefix]    like --solutions, and also ensure unsolved exercises do not pass
                       (optionally only exercises whose id starts with prefix, e.g. 03_)"

def findExercise (exs : Array Exercise) (q : String) : IO Exercise := do
  match exs.find? (·.matchesQuery q) with
  | some e => return e
  | none => throw <| IO.userError s!"No exercise named `{q}`. Try `lake exe leanlings list`."

def currentOrNamed (exs : Array Exercise) : List String → IO Exercise
  | [q] => findExercise exs q
  | _ => do
    match firstPending exs (← loadDone) with
    | some e => return e
    | none => throw <| IO.userError "All exercises are done!"

/-- Check all solutions. Returns the number of failures. -/
def verifySolutions (alsoExercises : Bool) (filter : Option String := none) : IO UInt32 := do
  let exs := (← discover).filter fun e => filter.all (e.id.startsWith ·)
  let mut failures := 0
  for e in exs do
    let o ← checkFile e e.solutionPath
    if o.isPassed then
      IO.println (green s!"✓ {e.id}")
    else
      failures := failures + 1
      IO.println (red s!"✗ solution of {e.id}")
      printOutcome e o e.solutionPath
    if alsoExercises then
      let o ← checkFile e e.exercisePath
      if o.isPassed then
        failures := failures + 1
        IO.println (red s!"✗ unsolved exercise {e.id} already passes!")
      if let .checkFailed out := o then
        failures := failures + 1
        IO.println (red s!"✗ checks of {e.id} do not fit the unsolved exercise:")
        IO.println out
  IO.println s!"{exs.size - failures} ok, {failures} failed"
  return if failures == 0 then 0 else 1

def verify : IO UInt32 := do
  let exs ← discover
  for e in exs do
    let o ← checkFile e e.exercisePath
    if o.isPassed then
      markDone e
      IO.println (green s!"✓ {e.id}")
    else
      markUndone e
      printOutcome e o
      return 1
  IO.println (green "All exercises pass!")
  return 0

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] | ["watch"] => watch; return 0
    | ["list"] =>
      let exs ← discover
      let done ← loadDone
      printProgress exs done
      printList exs done (firstPending exs done)
      return 0
    | "hint" :: rest =>
      let e ← currentOrNamed (← discover) rest
      IO.println (bold s!"Hint for {e.id}:")
      IO.println (← readHint e)
      return 0
    | "run" :: rest =>
      let e ← currentOrNamed (← discover) rest
      let o ← checkAndRecord e
      printOutcome e o
      return if o.isPassed then 0 else 1
    | ["verify"] => verify
    | ["verify", "--solutions"] => verifySolutions false
    | ["selftest"] => verifySolutions true
    | ["selftest", pre] => verifySolutions true (some pre)
    | ["reset", q] =>
      let e ← findExercise (← discover) q
      let r ← IO.Process.output { cmd := "git", args := #["checkout", "--", e.exercisePath.toString] }
      if r.exitCode != 0 then
        IO.eprintln r.stderr
        return 1
      markUndone e
      IO.println s!"Reset {e.exercisePath}."
      return 0
    | _ => IO.println usage; return if args == ["help"] || args == ["--help"] then 0 else 1
  catch err =>
    IO.eprintln (red s!"error: {err}")
    return 1
