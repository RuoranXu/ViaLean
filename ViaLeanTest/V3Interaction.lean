import ViaLean

open Lean Meta Elab Tactic ViaLean

#guard
  let action := nativeCloseAction
  let unknown : ModelSelection := { actionId? := some (action.fingerprint + 1) }
  let known : ModelSelection := { index? := some 0 }
  (SearchReplay.resolveAction unknown #[action]).isNone &&
    (SearchReplay.resolveAction known #[action]).isSome

#guard
  let hidden : FrontierProbe := {
    id := "hidden"
    perspective := "test"
    operation := "test"
    source := "test"
    result := "test"
    executable := false
  }
  let selection : ModelSelection := { probeIndex? := some 0 }
  (SearchReplay.resolveProbe selection #[hidden]).isNone

elab "v3_planner_workspace_exchange_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let base : ProposeConfig := {
      ai := true
      modelMode := "planner"
      modelProvider := "replay"
      plannerAllowExpansion := true
      frontierFutureDepth := 1
      frontierFutureWidth := 5
      atlasExpansionMaxDepth := 4
      atlasExpansionMaxWidth := 7
      atlasMaxNodes := 40
      atlasMaxTransitions := 48
      atlasMaxWorkUnits := 72
      atlasMaxMetaOps := 72
      atlasGuaranteedWork := 16
      atlasNeuralWork := 24
    }
    let workspace ← IO.mkRef ({} : ProofWorkspace)
    let some _ ← Workspace.observeGoal workspace base snap 0
      | throwError "planner exchange could not observe its root"
    let budget ← Budget.start 5
    discard <| FrontierEngine.expandWorkspace workspace snap base {
      maxDepth := 1
      maxWidthPerNode := 5
      workUnits := 16
      reason := "pre-neural-symbolic-tick"
    } (some budget)
    let before ← Workspace.refreshRegions workspace base.atlasMaxRegions
    let some region := before.atlas.regions[0]?
      | throwError "symbolic tick exposed no planner region"
    let response := (Json.mkObj [
      ("root_value", toJson (0.72 : Float)),
      ("confidence", toJson (0.61 : Float)),
      ("thoughts", Json.arr #[Json.mkObj [
        ("id", "helper-h"), ("kind", "exact"),
        ("expression_ref", "h"), ("dependencies", Json.arr #[])]]),
      ("strategy", Json.mkObj [
        ("primary_family", region.family.name),
        ("secondary_families", Json.arr #[Json.str "construction"]),
        ("horizon", 3), ("stop_condition", "close both constructor fields")]),
      ("expansion_requests", Json.arr #[Json.mkObj [
        ("region_id", toString region.id),
        ("family", region.family.name),
        ("extra_depth", 2), ("extra_width", 2),
        ("reason_code", "connect helper to constructor obligations")]])
    ]).compress
    let cfg := { base with modelReplayResponse := response }
    match ← PlannerEngine.query? workspace snap cfg budget with
    | .error error => throwError "valid planner exchange failed: {error}"
    | .ok decision =>
        unless decision.novelActions.size == 1 do
          throwError "thought batch was not compiled independently"
        unless decision.expansionResults.size == 1 do
          throwError "planner expansion request did not reach Atlas"
        unless decision.expansionRequests[0]!.reasonCode? == some "connect helper to constructor obligations" do
          throwError "planner expansion reason_code was not preserved"
        unless decision.strategy.horizon == 3 &&
            decision.strategy.secondaryFamilies == #["construction"] do
          throwError "multi-step strategy was not preserved"
    let after ← workspace.get
    unless after.version > before.version &&
        after.objects.any (fun object => object.status == .speculative) do
      throwError "model thought did not persist as a speculative Workspace object"
    let deltaView ← PlannerEngine.buildRequest workspace snap cfg 1000 {
      lastSeenVersion := before.version
      observationCount := before.observations.size
      primaryFamily? := some region.family.name
      confidence := 0.61
    }
    unless !deltaView.objects.isEmpty && !deltaView.observations.isEmpty do
      throwError "next neural epoch did not receive the Workspace delta"
    unless deltaView.objects.all (fun object => object.expression.startsWith "opaque:") do
      throwError "planner object view leaked a raw Lean expression"
    let badBudget ← Budget.start 2
    let badCfg := { cfg with modelReplayResponse := "{malformed" }
    match ← PlannerEngine.query? workspace snap badCfg badBudget with
    | .ok _ => throwError "malformed planner response crossed the trust boundary"
    | .error _ => pure ()
    unless !(← goal.isAssigned) do
      throwError "planner observation mutated the live proof goal"

example (P : Prop) (h : P) : P := by
  v3_planner_workspace_exchange_guard
  exact h

elab "v3_atlas_stress_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let rec addLocals (remaining : Nat) : MetaM Unit := do
      match remaining with
      | 0 =>
        let target ← goal.getType
        let stressGoal := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
        let snap ← snapshot stressGoal
        let cfg : ProposeConfig := {
          frontierFutureDepth := 3
          frontierFutureWidth := 8
          atlasExpansionMaxDepth := 3
          atlasExpansionMaxWidth := 8
          atlasMaxNodes := 12
          atlasMaxTransitions := 15
          atlasMaxWorkUnits := 18
          atlasMaxMetaOps := 18
          atlasMaxRenderedChars := 2048
        }
        let workspace ← IO.mkRef ({} : ProofWorkspace)
        discard <| Workspace.observeGoal workspace cfg snap 0
        let result ← FrontierEngine.expandWorkspace workspace snap cfg {
          maxDepth := 3
          maxWidthPerNode := 8
          workUnits := 18
          reason := "hundred-local-stress"
        }
        let after ← workspace.get
        unless after.atlas.nodes.size <= cfg.atlasMaxNodes &&
            after.atlas.transitions.size <= cfg.atlasMaxTransitions &&
            after.atlas.stats.transitionsTried <= cfg.atlasMaxWorkUnits &&
            after.atlas.stats.metaOps <= cfg.atlasMaxMetaOps &&
            after.atlas.nodes.all (fun node => node.depth <= 3) &&
            result.visitedNodes <= cfg.atlasMaxWorkUnits do
          throwError "Atlas exceeded a hard bound under 100-local pressure"
        unless !(← stressGoal.isAssigned) do
          throwError "stress preview assigned its source goal"
      | n + 1 =>
        withLocalDeclD (Name.mkSimple s!"stress_{n + 1}")
          (mkConst (Name.mkSimple "True")) fun _ =>
            addLocals n
    addLocals 100

example : True := by
  v3_atlas_stress_guard
  exact True.intro

elab "v3_instantiated_mvar_key_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let saved ← saveState
    let typeHole ← mkFreshExprMVar (mkSort (.succ .zero))
    let keyGoal := (← mkFreshExprSyntheticOpaqueMVar typeHole).mvarId!
    let before ← mkGoalKey keyGoal
    typeHole.mvarId!.assign (mkConst (Name.mkSimple "Nat"))
    let after ← mkGoalKey keyGoal
    let stable ← mkGoalKey keyGoal
    if before.strictEq after then
      throwError "GoalKey ignored an instantiated metavariable"
    unless after.strictEq stable do
      throwError "GoalKey was unstable after metavariable instantiation"
    saved.restore

example : True := by
  v3_instantiated_mvar_key_guard
  exact True.intro
