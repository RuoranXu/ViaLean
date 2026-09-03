import ViaLean.Model.Provider
import ViaLean.Workspace
import ViaLean.Planner.Conjecture

open Lean Meta

namespace ViaLean
namespace PlannerEngine

structure PlannerDecision where
  guidance : ModelGuidance
  novelActions : Array ProofAction := #[]
  leanCandidates : Array String := #[]
  expansionRequests : Array ModelProtocol.ExpansionRequest := #[]
deriving Inhabited

private def bounded (limit : Nat) (text : String) : String :=
  if text.length <= limit then text else (text.take limit).toString ++ "…"

private def shapeName : GoalShape → String
  | .equality => "equality" | .iff => "iff" | .conjunction => "conjunction"
  | .forall => "forall" | .exists => "exists" | .structure => "structure"
  | .proposition => "proposition" | .data => "data" | .other => "other"

private def outcomeName : TransitionOutcome → String
  | .untried => "untried" | .expanded => "expanded" | .solved => "solved"
  | .failed => "failed" | .timedOut => "timeout" | .rejected => "rejected"

private def failureName : FailureClass → String
  | .typeMismatch => "type_mismatch" | .unification => "unification"
  | .noProgress => "no_progress" | .branchGrowth => "branch_growth"
  | .timeout => "timeout" | .unsafeSyntax => "unsafe_syntax" | .unknown => "unknown"

def buildRequest (workspaceRef : IO.Ref ProofWorkspace) (snap : GoalSnapshot)
    (cfg : ProposeConfig) (remainingMs : Nat) : MetaM ModelProtocol.PlannerRequestV2 := do
  let workspace ← Workspace.refreshRegions workspaceRef cfg.atlasMaxRegions
  let atlas := workspace.atlas
  let rootId := (atlas.nodeForKey? snap.key).map (toString ·.id) |>.getD "0"
  let perNode := max 64 (cfg.atlasMaxRenderedChars / max 1 atlas.nodes.size)
  let mut nodes : Array ModelProtocol.PlannerNodeView := #[]
  for node in atlas.nodes do
    let goal ← node.snapshot.goalId.withContext do
      pure <| bounded perNode (← ppExpr node.snapshot.target).pretty
    nodes := nodes.push {
      id := toString node.id
      depth := node.depth
      goal
      subgoals := node.signals.subgoals
      exactLocal := node.signals.exactLocal
      contradiction := node.signals.contradiction
    }
  let regions : Array ModelProtocol.PlannerRegionView := atlas.regions.map fun region => {
    id := toString region.id
    family := region.family.name
    size := region.size
    signals := #[s!"solved={region.signals.solved}", s!"failed={region.signals.failed}",
      s!"exact_local={region.signals.exactLocal}"]
    representatives := region.representative.map toString
  }
  let transitions : Array ModelProtocol.PlannerTransitionView := atlas.transitions.map fun transition => {
    id := toString transition.id
    sourceId := toString transition.parent
    targetIds := transition.children.map toString
    family := transition.candidate.family.name
    operation := transition.candidate.operation.name
    cost := transition.candidate.estimatedCost
    executable := transition.executable
  }
  let observationStart := workspace.observations.size - min workspace.observations.size cfg.modelMaxFeedbackEvents
  let observations : Array ModelProtocol.PlannerObservationView :=
      (workspace.observations.extract observationStart workspace.observations.size).map fun observation => {
    transition? := observation.transition?.map toString
    outcome := outcomeName observation.outcome
    failureClass? := observation.failureClass?.map failureName
  }
  let usedWork := min cfg.atlasMaxWorkUnits atlas.stats.transitionsTried
  let budgetView : ModelProtocol.PlannerBudgetView := {
    remainingMs := remainingMs
    remainingAtlasWork := cfg.atlasMaxWorkUnits - usedWork
  }
  let rootView : ModelProtocol.PlannerRootView := {
    id := rootId
    shape := shapeName snap.shape
    goal := bounded perNode (← ppExpr snap.target).pretty
  }
  return {
    requestId := s!"{snap.fingerprint}/{workspace.version}"
    workspaceVersion := workspace.version
    budget := budgetView
    root := rootView
    regions
    nodes
    transitions
    observations
  }

private def insertMax (scores : Std.HashMap UInt64 Float) (id : UInt64) (score : Float) :=
  scores.insert id (max score ((scores.get? id).getD 0.0))

def toGuidance (atlas : ProofAtlas) (response : ModelProtocol.PlannerResponseV2)
    (allowExpansion : Bool := true) : ModelGuidance :=
  let regionScores := response.preferredRegions.foldl (init := {}) fun scores signal =>
    match signal.id.toNat? with
    | none => scores
    | some id =>
      match atlas.regions.find? (·.id == UInt64.ofNat id) with
      | none => scores
      | some region => atlas.transitions.foldl (init := scores) fun scores transition =>
          if transition.candidate.family == region.family then
            insertMax scores transition.candidate.fingerprint (ModelProtocol.clamp01 signal.score)
          else scores
  let strategyScores := match response.strategy.primaryFamily? with
    | none => regionScores
    | some family => atlas.transitions.foldl (init := regionScores) fun scores transition =>
        if transition.candidate.family.name == family then
          insertMax scores transition.candidate.fingerprint 0.7
        else scores
  let expansionScores := if !allowExpansion then strategyScores else
    response.expansionRequests.foldl (init := strategyScores) fun scores request =>
      match request.family? with
      | none => scores
      | some family => atlas.transitions.foldl (init := scores) fun scores transition =>
          if transition.candidate.family.name == family then
            insertMax scores transition.candidate.fingerprint 0.75
          else scores
  let scores := response.transitionScores.foldl (init := expansionScores) fun scores signal =>
    match signal.id.toNat? with
    | none => scores
    | some id =>
        match atlas.transition? (UInt64.ofNat id) with
        | none => scores
        | some transition =>
            let score := 0.45 * signal.policy + 0.45 * signal.value +
              0.10 * signal.confidence
            insertMax scores transition.candidate.fingerprint (ModelProtocol.clamp01 score)
  { value := ModelProtocol.clamp01 response.rootValue
    actionScores := scores
    rationale? := response.strategy.objective? }

def query? (workspace : IO.Ref ProofWorkspace) (snap : GoalSnapshot)
    (cfg : ProposeConfig) (budget : Budget) : MetaM (Except String PlannerDecision) := do
  let remainingMs ← budget.remainingMs
  if remainingMs == 0 then return .error "planner has no remaining budget"
  let request ← buildRequest workspace snap cfg remainingMs
  let timeoutMs := min remainingMs cfg.modelTimeoutMs
  match ← ModelProvider.queryPlanner cfg request timeoutMs with
  | .error error => return .error error
  | .ok response =>
      let (proposals, batch) ← ConjectureEngine.compile snap cfg response.thoughts
      let current ← workspace.get
      let batch := { batch with epoch := current.neuralEpoch + 1 }
      discard <| Workspace.absorbThoughtBatch workspace batch
      let current ← workspace.get
      return .ok {
        guidance := toGuidance current.atlas response cfg.plannerAllowExpansion
        novelActions := proposals.map Proposal.compile
        leanCandidates := response.leanCandidates
        expansionRequests := response.expansionRequests
      }

end PlannerEngine
end ViaLean
