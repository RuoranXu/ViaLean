import ViaLean.Scheduler.Basic

open Lean

namespace ViaLean

structure PersistedFamilyStats where
  family    : String
  attempts  : Nat
  rewardSum : Float
deriving ToJson, FromJson, Inhabited

structure PersistentStats where
  version  : Nat := 1
  families : Array PersistedFamilyStats := #[]
deriving ToJson, FromJson, Inhabited

def loadPersistentStats (path : System.FilePath) : IO PersistentStats := do
  if !(← path.pathExists) then return {}
  try
    let text ← IO.FS.readFile path
    match Json.parse text >>= fromJson? with
    | .ok stats => return stats
    | .error _ => return {}
  catch _ => return {}

/-- Stores aggregate counters only; raw goals and source text are not accepted by this DTO. -/
def savePersistentStats (path : System.FilePath) (stats : PersistentStats) : IO Unit :=
  IO.FS.writeFile path (toJson stats).pretty

end ViaLean
