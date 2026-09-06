import ViaLean.Config

open Lean

namespace ViaLean

initialize Lean.registerTraceClass `ViaLean
initialize Lean.registerTraceClass `ViaLean.proposal
initialize Lean.registerTraceClass `ViaLean.scheduler
initialize Lean.registerTraceClass `ViaLean.native
initialize Lean.registerTraceClass `ViaLean.external

structure TrainingTraceEvent where
  sequence : Nat
  kind : String
  workspaceVersion : Nat
  payload : Json := Json.mkObj []
deriving Inhabited

def TrainingTraceEvent.toJson (event : TrainingTraceEvent) : Json := Json.mkObj [
  ("schema", "vialean.training.v3"),
  ("sequence", event.sequence),
  ("kind", event.kind),
  ("workspace_version", event.workspaceVersion),
  ("payload", event.payload)
]

def pushTrainingEvent (ref : IO.Ref (Array TrainingTraceEvent))
    (kind : String) (workspaceVersion : Nat) (payload : Json := Json.mkObj []) :
    IO Unit := do
  let events ← ref.get
  ref.set <| events.push {
    sequence := events.size
    kind
    workspaceVersion
    payload
  }

/-- Write a deterministic, redacted JSONL trace. Callers supply IDs, counts and
scores only; raw goals, local names and source text are intentionally excluded. -/
def writeTrainingJsonl (pathText : String) (events : Array TrainingTraceEvent)
    (maxEvents : Nat) : IO Unit := do
  if pathText.isEmpty then return
  let selected := events.take maxEvents
  let lines := selected.map fun event => event.toJson.compress
  let text := String.intercalate "\n" lines.toList
  IO.FS.writeFile (System.FilePath.mk pathText)
    (if text.isEmpty then text else text ++ "\n")

end ViaLean
