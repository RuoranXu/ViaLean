import ViaLean

open Lean Meta Elab Tactic ViaLean

#guard
  let event : TrainingTraceEvent := {
    sequence := 3
    kind := "planner"
    workspaceVersion := 7
    payload := Json.mkObj [("value", toJson (0.75 : Float))]
  }
  match Json.parse event.toJson.compress with
  | .ok json =>
      (json.getObjVal? "schema").toOption.bind (·.getStr?.toOption) ==
        some "vialean.training.v3"
  | .error _ => false

elab "v3_shared_atlas_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let cfg : ProposeConfig := {
      frontierFutureDepth := 1
      frontierFutureWidth := 6
      atlasExpansionMaxDepth := 5
      atlasExpansionMaxWidth := 8
      atlasMaxNodes := 48
      atlasMaxTransitions := 64
      atlasMaxWorkUnits := 96
      atlasMaxMetaOps := 96
      atlasGuaranteedWork := 24
      atlasNeuralWork := 32
    }
    let workspace ← IO.mkRef ({} : ProofWorkspace)
    let some root ← Workspace.observeGoal workspace cfg snap 0
      | throwError "shared Atlas rejected its root"
    let budget ← Budget.start 5
    let first ← FrontierEngine.expandWorkspace workspace snap cfg {
      maxDepth := 1
      maxWidthPerNode := 6
      workUnits := 24
      reason := "characterization"
    } (some budget)
    let afterFirst ← Workspace.refreshRegions workspace cfg.atlasMaxRegions
    unless first.addedTransitions > 0 && afterFirst.atlas.nodes.size > 1 do
      throwError "symbolic future was not materialized into the shared Atlas"
    unless afterFirst.atlas.nodes.any fun node =>
        node.preview && !node.renderedGoal.isEmpty do
      throwError "preview nodes lost their durable goal/context rendering"
    let replayWorkspace ← IO.mkRef ({} : ProofWorkspace)
    discard <| Workspace.observeGoal replayWorkspace cfg snap 0
    let replayBudget ← Budget.start 5
    discard <| FrontierEngine.expandWorkspace replayWorkspace snap cfg {
      maxDepth := 1
      maxWidthPerNode := 6
      workUnits := 24
      reason := "deterministic-replay"
    } (some replayBudget)
    let replayState ← Workspace.refreshRegions replayWorkspace cfg.atlasMaxRegions
    let nodeOrder := afterFirst.atlas.nodes.map fun node =>
      (node.id, node.depth, node.key.bucket)
    let replayNodeOrder := replayState.atlas.nodes.map fun node =>
      (node.id, node.depth, node.key.bucket)
    let transitionOrder := afterFirst.atlas.transitions.map fun transition =>
      (transition.id, transition.parent, transition.candidate.fingerprint)
    let replayTransitionOrder := replayState.atlas.transitions.map fun transition =>
      (transition.id, transition.parent, transition.candidate.fingerprint)
    unless nodeOrder == replayNodeOrder && transitionOrder == replayTransitionOrder do
      throwError "deterministic Atlas replay changed IDs or transition ordering"
    let some region := afterFirst.atlas.regions.find? (·.family == .structural)
      | throwError "family-diverse Atlas did not expose the structural region"
    let expansion ← PlannerEngine.executeExpansionRequests workspace snap cfg budget #[{
      regionId := toString region.id
      family? := some "structural"
      extraDepth := 3
      extraWidth := 2
      reasonCode? := some "follow nested binders"
    }]
    let afterExpansion ← workspace.get
    unless expansion.any fun result =>
        result.addedNodes > 0 || result.addedTransitions > 0 do
      let nodes := afterExpansion.atlas.nodes.map fun node => (node.id, node.depth, node.key.bucket)
      let transitions := afterExpansion.atlas.transitions.map fun transition =>
        (transition.id, transition.parent, transition.candidate.family, transition.candidate.fingerprint)
      throwError "planner expansion did not allocate work: {repr expansion}; nodes={repr nodes}; transitions={repr transitions}"
    unless afterExpansion.atlas.stats.metaOps <= cfg.atlasMaxMetaOps &&
        afterExpansion.atlas.transitions.size <= cfg.atlasMaxTransitions do
      throwError "planner expansion exceeded a global Atlas bound"
    let initial := ReplanEngine.decide cfg afterExpansion snap.key {}
    unless initial.openEpoch && initial.cause == .initial do
      throwError "initial neural epoch was not opened"
    let cursor := ReplanEngine.advance afterExpansion snap.key 0.8 {} {}
    if (ReplanEngine.decide cfg afterExpansion snap.key cursor).openEpoch then
      throwError "unchanged semantic Atlas triggered a duplicate planner query"
    discard <| Workspace.registerObject workspace .helperLemma snap.target
      none .pending .derived #[] #[] 0.9
    let changed ← workspace.get
    unless (ReplanEngine.decide cfg changed snap.key cursor).openEpoch do
      throwError "new high-value Workspace object did not trigger replanning"
    unless !(← goal.isAssigned) do
      throwError "Atlas observation leaked an assignment into the live goal"
    unless afterExpansion.atlas.node? root |>.isSome do
      throwError "root node disappeared during incremental expansion"

example (P Q : Prop) : P → Q → P := by
  v3_shared_atlas_guard
  intro hp _
  exact hp

/-- Core-only real inhabitation pattern: two local functions must be composed.
The native/direct lane is disabled, so this is closed by the ubiquitous LocalSynth engine. -/
example (A B C : Prop) (ab : A → B) (bc : B → C) (a : A) : C := by
  propose
    (directProbeSec := 0)
    (finalDirectMinSec := 0)
    (frontier := false)
    (structural := false)
    (cuts := false)
    (library := false)
    (equalityBridge := false)
    (iffBridge := false)
    (witnesses := false)
    (nativeTransforms := false)
    (nativeCases := false)
    (localSynthDepth := 3)
    (maxDepth := 0)

elab "v3_thought_dependency_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let valid : Array ModelProtocol.PlannerThoughtView := #[
      { id := "seed", kind := "exact", expressionRef := "h" },
      { id := "dependent", kind := "exact", expressionRef := "h",
        dependencies := #["seed"] }
    ]
    let (proposals, batch) ← ConjectureEngine.compile snap {} valid
    unless proposals.size == 2 && batch.thoughts.size == 2 do
      throwError "ordered thought dependencies were not preserved"
    let invalid : Array ModelProtocol.PlannerThoughtView := #[
      { id := "blocked", kind := "exact", expressionRef := "h",
        dependencies := #["missing"] }
    ]
    let (blocked, _) ← ConjectureEngine.compile snap {} invalid
    unless blocked.isEmpty do
      throwError "thought with an unresolved dependency was executed"

example (P : Prop) (h : P) : P := by
  v3_thought_dependency_guard
  exact h
