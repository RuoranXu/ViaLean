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
  strategy : ModelProtocol.StrategyPlan := {}
  confidence : Float := 0.5
  expansionResults : Array FrontierEngine.AtlasExpansionResult := #[]
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
  | .branchExplosion => "branch_explosion" | .timeout => "timeout"
  | .unsafeSyntax => "unsafe_syntax" | .rewriteNoMatch => "rewrite_no_match"
  | .premiseMismatch => "premise_mismatch" | .openGoals => "open_goals"
  | .invalidPlannerSelection => "invalid_planner_selection"
  | .budgetDenied => "budget_denied" | .internal => "internal"
  | .unknown => "unknown"

private def statusName : KnowledgeStatus → String
  | .verified => "verified" | .pending => "pending"
  | .speculative => "speculative" | .refuted => "refuted"
  | .dominated => "dominated"

private def conjectureKindName : ConjectureKind → String
  | .helperLemma => "helper_lemma" | .equalityBridge => "equality_bridge"
  | .iffBridge => "iff_bridge" | .witness => "witness"
  | .invariant => "invariant" | .generalization => "generalization"
  | .term => "term"

def buildRequest (workspaceRef : IO.Ref ProofWorkspace) (snap : GoalSnapshot)
    (cfg : ProposeConfig) (remainingMs : Nat)
    (memory : ModelProtocol.PlannerMemoryView := {}) : MetaM ModelProtocol.PlannerRequestV2 := do
  let workspace ← Workspace.refreshRegions workspaceRef cfg.atlasMaxRegions
  let atlas := workspace.atlas
  let rootId := (atlas.nodeForKey? snap.key).map (toString ·.id) |>.getD "0"
  let perNode := max 64 (cfg.atlasMaxRenderedChars / max 1 atlas.nodes.size)
  let mut nodes : Array ModelProtocol.PlannerNodeView := #[]
  for node in atlas.nodes do
    let goal ← if !node.renderedGoal.isEmpty then
      pure <| bounded perNode node.renderedGoal
    else node.snapshot.goalId.withContext do
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
  let feedbackStart :=
    workspace.observations.size - min workspace.observations.size cfg.modelMaxFeedbackEvents
  let observationStart := max feedbackStart (min memory.observationCount workspace.observations.size)
  let observations : Array ModelProtocol.PlannerObservationView :=
      (workspace.observations.extract observationStart workspace.observations.size).map fun observation => {
    transition? := observation.transition?.map toString
    outcome := outcomeName observation.outcome
    failureClass? := observation.failureClass?.map failureName
  }
  let orderedObjects := workspace.objects.insertionSort fun left right =>
    if left.utility == right.utility then left.id.toNat < right.id.toNat
    else left.utility > right.utility
  let objects : Array ModelProtocol.PlannerObjectView :=
    (orderedObjects.take cfg.localSynthMaxTerms).map fun object => {
      id := toString object.id
      kind := conjectureKindName object.kind
      status := statusName object.status
      expression := s!"opaque:{object.id}"
      type? := none
      blockers := object.blockers.map toString
      utility := object.utility
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
    objects
    memory
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
  let scoreFamily (scores : Std.HashMap UInt64 Float)
      (family : String) (score : Float) :=
    atlas.transitions.foldl (init := scores) fun scores transition =>
      if transition.candidate.family.name == family then
        insertMax scores transition.candidate.fingerprint score
      else scores
  let strategyScores := match response.strategy.primaryFamily? with
    | none => regionScores
    | some family => scoreFamily regionScores family 0.7
  let strategyScores := response.strategy.secondaryFamilies.foldl
    (init := strategyScores) fun scores family => scoreFamily scores family 0.62
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

private def expansionRegion? (atlas : ProofAtlas)
    (request : ModelProtocol.ExpansionRequest) : Option ProofRegion :=
  request.regionId.toNat?.bind fun id =>
    atlas.regions.find? (·.id == UInt64.ofNat id)

def executeExpansionRequests (workspace : IO.Ref ProofWorkspace) (snap : GoalSnapshot)
    (cfg : ProposeConfig) (budget : Budget)
    (requests : Array ModelProtocol.ExpansionRequest) :
    MetaM (Array FrontierEngine.AtlasExpansionResult) := do
  if !cfg.plannerAllowExpansion || requests.isEmpty then return #[]
  let workspaceView ← Workspace.refreshRegions workspace cfg.atlasMaxRegions
  let workPerRequest := if cfg.atlasNeuralWork = 0 then 0
    else max 1 (cfg.atlasNeuralWork / max 1 requests.size)
  let mut results := #[]
  for request in requests do
    if (← budget.remainingMs) = 0 then break
    let region? := expansionRegion? workspaceView.atlas request
    let family? := request.family?.bind StrategyFamily.ofName?
    if region?.isNone || (request.family?.isSome && family?.isNone) then
      Workspace.recordObservation workspace .rejected (some .invalidPlannerSelection)
        (debug? := some s!"invalid expansion region/family: {request.regionId}/{request.family?}")
      results := results.push {
        fromVersion := workspaceView.version, toVersion := workspaceView.version
        budgetDenied := true }
      continue
    let family := family?.orElse (fun _ => region?.map (·.family))
    let baseDepth := min cfg.frontierFutureDepth cfg.atlasExpansionMaxDepth
    let requestedDepth := min cfg.atlasExpansionMaxDepth
      (baseDepth + min request.extraDepth cfg.atlasExpansionMaxDepth)
    let requestedWidth := min cfg.atlasExpansionMaxWidth
      (max 1 (cfg.frontierFutureWidth + request.extraWidth))
    let result ← FrontierEngine.expandWorkspace workspace snap cfg {
      family? := family
      maxDepth := requestedDepth
      maxWidthPerNode := requestedWidth
      workUnits := workPerRequest
      reason := request.reasonCode?.getD "planner-request"
    } (some budget)
    let useful := result.addedNodes > 0 || result.addedTransitions > 0
    Workspace.recordObservation workspace
      (if useful then .expanded else if result.budgetDenied then .rejected else .failed)
      (if result.budgetDenied then some .budgetDenied
       else if useful then none else some .noProgress)
      (debug? := some s!"expansion {request.regionId}: +{result.addedNodes} nodes, +{result.addedTransitions} transitions")
    results := results.push result
  return results

def query? (workspace : IO.Ref ProofWorkspace) (snap : GoalSnapshot)
    (cfg : ProposeConfig) (budget : Budget)
    (memory : ModelProtocol.PlannerMemoryView := {}) : MetaM (Except String PlannerDecision) := do
  let remainingMs ← budget.remainingMs
  if remainingMs == 0 then return .error "planner has no remaining budget"
  let request ← buildRequest workspace snap cfg remainingMs memory
  let timeoutMs := min remainingMs cfg.modelTimeoutMs
  match ← ModelProvider.queryPlanner cfg request timeoutMs with
  | .error error => return .error error
  | .ok response =>
      let beforeCompile ← workspace.get
      let (proposals, batch) ← ConjectureEngine.compile snap cfg response.thoughts beforeCompile.objects
      let current ← workspace.get
      let batch := { batch with epoch := current.neuralEpoch + 1 }
      discard <| Workspace.absorbThoughtBatch workspace batch
      let expansionResults ← executeExpansionRequests
        workspace snap cfg budget response.expansionRequests
      let current ← workspace.get
      return .ok {
        guidance := toGuidance current.atlas response cfg.plannerAllowExpansion
        novelActions := proposals.map Proposal.compile
        leanCandidates := response.leanCandidates
        expansionRequests := response.expansionRequests
        strategy := response.strategy
        confidence := response.confidence
        expansionResults
      }

end PlannerEngine
end ViaLean
