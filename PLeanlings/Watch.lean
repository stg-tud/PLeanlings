import PLeanlings.UI

/-!
# Watch mode

Polls the current exercise's modification time and re-checks it on change.
Commands are read line-by-line from stdin on a separate thread.
-/

namespace PLeanlings

private def mtime (p : System.FilePath) : IO IO.FS.SystemTime := do
  return (← p.metadata).modified

private def showCurrent (exs : Array Exercise) (e : Exercise) (o : Outcome) : IO Unit := do
  clearScreen
  printProgress exs (← loadDone)
  IO.println s!"Current exercise: {bold e.exercisePath.toString}"
  IO.println ""
  printOutcome e o
  IO.println ""
  IO.println (dim "Commands (type + Enter):  h = hint   l = list   r = re-check   q = quit")

/-- Check `e`; on success mark it done. -/
def checkAndRecord (e : Exercise) : IO Outcome := do
  let o ← checkFile e e.exercisePath
  if o.isPassed then markDone e
  return o

/-- Move to the first pending exercise, skipping any that already pass. -/
private partial def advance (exs : Array Exercise) : IO (Option (Exercise × Outcome)) := do
  match firstPending exs (← loadDone) with
  | none => return none
  | some e =>
    IO.println s!"Checking {e.id} …"
    let o ← checkAndRecord e
    if o.isPassed then advance exs else return some (e, o)

private partial def loop (exs : Array Exercise) (cmds : IO.Ref (Array String))
    (cur : Exercise) (lastTime : IO.FS.SystemTime) : IO Unit := do
  IO.sleep 300
  let pending ← cmds.modifyGet fun cs => (cs, #[])
  let mut recheck := false
  for c in pending do
    match c with
    | "q" | "quit" => IO.println "Bye! Your progress is saved."; return
    | "h" | "hint" =>
      IO.println ""
      IO.println (bold "Hint:")
      IO.println (← readHint cur)
    | "l" | "list" => printList exs (← loadDone) (some cur)
    | "r" | "run" | "" => recheck := true
    | other => IO.println s!"Unknown command `{other}`."
  let t ← mtime cur.exercisePath
  if t == lastTime && !recheck then
    return ← loop exs cmds cur t
  IO.println (dim s!"Checking {cur.id} …")
  let o ← checkAndRecord cur
  showCurrent exs cur o
  unless o.isPassed do
    return ← loop exs cmds cur t
  IO.sleep 1500
  match ← advance exs with
  | none =>
    IO.println ""
    IO.println (green (bold "🎉 Congratulations! You have finished all PLeanlings exercises."))
  | some (e, o) =>
    showCurrent exs e o
    loop exs cmds e (← mtime e.exercisePath)

def watch : IO Unit := do
  let exs ← discover
  let cmds ← IO.mkRef (#[] : Array String)
  let stdin ← IO.getStdin
  let _ ← IO.asTask (prio := .dedicated) do
    repeat
      let l ← stdin.getLine
      if l.isEmpty then break -- EOF
      cmds.modify (·.push l.trimAscii.toString)
  match ← advance exs with
  | none => IO.println (green "All exercises are done! 🎉")
  | some (e, o) =>
    showCurrent exs e o
    loop exs cmds e (← mtime e.exercisePath)

end PLeanlings
