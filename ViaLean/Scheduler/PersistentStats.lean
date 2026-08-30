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
    if (← path.metadata).byteSize > 1048576 then return {}
    let text ← IO.FS.readFile path
    match Json.parse text >>= fromJson? with
    | .ok stats => return stats
    | .error _ => return {}
  catch _ => return {}

/-- Stores aggregate counters only; raw goals and source text are not accepted by this DTO. -/
def savePersistentStats (path : System.FilePath) (stats : PersistentStats) : IO Unit :=
  IO.FS.writeFile path (toJson stats).pretty

private def familyName : ProposalFamily → String
  | .direct => "direct"
  | .structural => "structural"
  | .localCut => "localCut"
  | .libraryCut => "libraryCut"
  | .equalityNormalize => "equalityNormalize"
  | .equalityLocal => "equalityLocal"
  | .equalityExternal => "equalityExternal"
  | .witnessLocal => "witnessLocal"
  | .witnessExternal => "witnessExternal"
  | .externalCut => "externalCut"

private def parseFamily? : String → Option ProposalFamily
  | "direct" => some .direct
  | "structural" => some .structural
  | "localCut" => some .localCut
  | "libraryCut" => some .libraryCut
  | "equalityNormalize" => some .equalityNormalize
  | "equalityLocal" => some .equalityLocal
  | "equalityExternal" => some .equalityExternal
  | "witnessLocal" => some .witnessLocal
  | "witnessExternal" => some .witnessExternal
  | "externalCut" => some .externalCut
  | _ => none

/-- Seed a scheduler from aggregate counters; malformed or unknown families are ignored. -/
def PersistentStats.seedScheduler
    (persisted : PersistentStats) (scheduler : SchedulerState) : IO Unit :=
  scheduler.stats.modify fun stats => persisted.families.foldl (init := stats) fun stats entry =>
    match parseFamily? entry.family with
    | none => stats
    | some family => stats.insert family {
        attempts := entry.attempts
        rewardSum := entry.rewardSum
      }

/-- Export only aggregate scheduler counters for optional persistence. -/
def SchedulerState.toPersistentStats (scheduler : SchedulerState) : IO PersistentStats := do
  let stats ← scheduler.snapshot
  let families := stats.fold (init := #[]) fun result family familyStats =>
    result.push {
      family := familyName family
      attempts := familyStats.attempts
      rewardSum := familyStats.rewardSum
    }
  return { families }

end ViaLean
