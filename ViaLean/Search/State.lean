import ViaLean.Fingerprint
import ViaLean.Scheduler.Basic
import ViaLean.Model.Protocol
import ViaLean.Solver.Router
import ViaLean.Workspace
import ViaLean.Trace

import ViaLean.Search.Replan
open Lean Meta

namespace ViaLean

structure SolveStats where
  directAttempts : Nat := 0
  proposalAttempts : Nat := 0
  modelCalls : Nat := 0
  replanCount : Nat := 0
  atlasNodes : Nat := 0
  atlasTransitions : Nat := 0
  atlasMetaOps : Nat := 0
  bridgeDepth : Nat := 0
  elapsedMs : Nat := 0
  winningFamily? : Option ProposalFamily := none
deriving Inhabited

inductive SolveResult
  | solved (proof : Expr) (stats : SolveStats)
  | failed (stats : SolveStats)

structure SearchState where
  config : ProposeConfig
  budget : Budget
  scheduler : SchedulerState
  guidanceCache : IO.Ref (Std.HashMap UInt64 (Option ModelGuidance))
  feedback : IO.Ref (Array SearchFeedback)
  traceEvents : IO.Ref (Array TrainingTraceEvent)
  stats : IO.Ref SolveStats
  router : LeafRouter
  plannerCursor : IO.Ref PlannerCursor
  workspace : IO.Ref ProofWorkspace
  plannerVersions : IO.Ref (Std.HashMap UInt64 Nat)
  plannerCalls : IO.Ref Nat
  activeTransition? : Option TransitionId := none
  path : SearchPath := {}
  maxLeafSec? : Option Nat := none
  modelEnabled : Bool := true

end ViaLean
