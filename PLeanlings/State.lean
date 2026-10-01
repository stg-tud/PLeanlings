import PLeanlings.Exercise

/-! Progress is stored as one exercise id per line in `.pleanlings-state`. -/

namespace PLeanlings

def stateFile : System.FilePath := ".pleanlings-state"

def loadDone : IO (List String) := do
  unless ← stateFile.pathExists do return []
  let s ← IO.FS.readFile stateFile
  return (s.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

def saveDone (done : List String) : IO Unit :=
  IO.FS.writeFile stateFile (String.intercalate "\n" done ++ "\n")

def markDone (e : Exercise) : IO Unit := do
  let done ← loadDone
  unless done.contains e.id do saveDone (done ++ [e.id])

def markUndone (e : Exercise) : IO Unit := do
  saveDone ((← loadDone).filter (· != e.id))

/-- The first exercise that is not done yet (core exercises before bonus ones). -/
def firstPending (exs : Array Exercise) (done : List String) : Option Exercise :=
  exs.find? (fun e => !e.isBonus && !done.contains e.id)
    |>.orElse fun _ => exs.find? (fun e => !done.contains e.id)

end PLeanlings
