import ViaLean.Search.State
import ViaLean.Scheduler.UCB
import ViaLean.Planner.Conjecture

open Lean Meta

namespace ViaLean.SearchDecision

def modelMode (state : SearchState) : String :=
  state.config.modelMode.trimAscii.toString.toLower

def feedbackActionName (action : ProofAction) : String :=
  match action.payload with
  | .close solver => s!"close/{(repr solver).pretty}"
  | .structural rule => s!"structural/{(repr rule).pretty}"
  | .proposal proposal => s!"{(repr proposal.kind).pretty}/{proposal.source}"
  | .sketch holes => s!"sketch/{holes.size}"

def failureClassFor (action : ProofAction) : FailureClass :=
  match action.payload with
  | .close _ => .noProgress
  | .structural _ => .branchGrowth
  | .sketch _ => .openGoals
  | .proposal proposal =>
      match proposal.payload with
      | .libraryApply _ => .premiseMismatch
      | .equalityMid _ | .iffMid _ => .unification
      | .witness _ => .typeMismatch
      | .cutType _ => .openGoals
      | .directTerm _ | .structural _ => .noProgress

def plannerThoughtId? (action : ProofAction) : Option UInt64 :=
  match action.payload with
  | .proposal proposal =>
      if proposal.origin == .planner then
        (proposal.source.splitOn ":").reverse.head?.map ConjectureEngine.thoughtId
      else none
  | _ => none

def orderActions
    (state : SearchState) (guidance? : Option ModelGuidance)
    (actions : Array ProofAction) : MetaM (Array ProofAction) := do
  let stats ← state.scheduler.snapshot
  let total := stats.fold (init := 0) fun total _ family =>
    total + family.attempts
  let baseScore (action : ProofAction) :=
    if state.config.rankingMode == .ucb ||
        state.config.rankingMode == .hybrid then
      let familyStats := (stats.get? action.family).getD {}
      ucbScore familyStats total action.prior
        state.config.ucbExploration state.config.ucbPriorWeight
    else action.prior
  let score (action : ProofAction) :=
    let base := baseScore action
    let actionSignal? := guidance?.bind fun guidance =>
      ModelProtocol.ModelGuidance.score? guidance action.fingerprint
    let signal? := match actionSignal? with
      | some signal => some signal
      | none => guidance?.map (·.value)
    let blended :=
      ModelProtocol.blendScore base signal? state.config.modelWeight
    blended / max 0.1 action.estimatedCost
  return actions.insertionSort fun a b =>
    if score a == score b then
      if state.config.stableTieBreak then false
      else a.fingerprint < b.fingerprint
    else score a > score b

end ViaLean.SearchDecision
