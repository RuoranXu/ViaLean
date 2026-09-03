import ViaLean

open Lean Meta Elab Tactic ViaLean

#guard
  let huge := String.ofList (List.replicate 12000 'x')
  let request : InteractionRequest := {
    requestId := "cap-test"
    round := 0
    depth := 0
    shape := "proposition"
    target := huge
    locals := #[huge, huge]
    actions := #[]
    frontier := #[]
    feedback := #[]
  }
  let payload := ModelProtocol.interactionRequestTextCapped request 256
  payload.length <= 256 && (Json.parse payload).isOk

#guard
  let huge := String.ofList (List.replicate 12000 'g')
  let request : ModelProtocol.PlannerRequestV2 := {
    requestId := "planner-cap"
    workspaceVersion := 7
    budget := { remainingMs := 1000, remainingAtlasWork := 20 }
    root := { id := "0", shape := "equality", goal := huge }
  }
  let payload := ModelProtocol.plannerRequestTextCapped request 256
  payload.length <= 256 && (Json.parse payload).isOk

#guard
  match ModelProtocol.parsePlannerResponse
      r#"{"root_value":0.8,"confidence":0.7,"transition_scores":[{"id":"3","policy":0.9,"value":0.6,"confidence":0.8}],"strategy":{"primary_family":"equality","objective":"join the chain"},"expansion_requests":[{"region_id":"9","extra_depth":1,"family":"equality"}]}"# with
  | .ok response => response.rootValue == 0.8 && response.confidence == 0.7 &&
      response.transitionScores.size == 1 && response.expansionRequests.size == 1 &&
      response.strategy.primaryFamily? == some "equality"
  | .error _ => false

#guard
  match ModelProtocol.parsePlannerResponse
      r#"{"thoughts":[{"id":"11","kind":"equality_bridge","expression_ref":"b","dependencies":["2"]}],"lean_candidates":[{"code":"by exact h"}]}"# with
  | .ok response => response.thoughts.size == 1 &&
      response.thoughts[0]!.expressionRef == "b" &&
      response.thoughts[0]!.dependencies == #["2"] &&
      response.leanCandidates == #["by exact h"]
  | .error _ => false

syntax "v3_custom_tactic" : tactic
macro_rules | `(tactic| v3_custom_tactic) => `(tactic| exact True.intro)

elab "v3_sandbox_guard" : tactic => do
  let env ← getEnv
  let invalidInputs := #[
    "by run_tac IO.println \"unsafe\"",
    "by set_option pp.all true in exact True.intro",
    "by v3_custom_tactic",
    "by exact `(not_a_term)",
    "by this is malformed"
  ]
  for code in invalidInputs do
    if (parseSafeModelTactic env code).isOk then
      throwError "unsafe or unsupported model code passed: {code}"
  match parseSafeModelTactic env "by exact True.intro" with
  | .error error => throwError "reviewed exact tactic was rejected: {error}"
  | .ok _ => pure ()

example : True := by
  v3_sandbox_guard
  exact True.intro

elab "v3_goal_key_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let natType := mkConst ``Nat
    let keyWithLocal (name : Name) : MetaM GoalKey :=
      withLocalDeclD name target fun _ => do
        let fresh := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
        mkGoalKey fresh
    let left ← keyWithLocal `leftName
    let renamed ← keyWithLocal `renamedLocal
    unless left.strictEq renamed do
      throwError "GoalKey is not alpha-renaming invariant"
    let keyWithLet (value : Nat) : MetaM GoalKey :=
      withLetDecl `x natType (mkNatLit value) fun _ => do
        let fresh := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
        mkGoalKey fresh
    let zero ← keyWithLet 0
    let one ← keyWithLet 1
    if zero.strictEq one then
      throwError "GoalKey discarded let-value semantics"
    let forced := ({} : StrictGoalSet).insertAt 42 zero
    unless forced.containsAt 42 zero do
      throwError "strict goal set lost an inserted key"
    if forced.containsAt 42 one then
      throwError "hash collision bypassed structural GoalKey confirmation"
    let keyWithOrder (first second : Expr) : MetaM GoalKey :=
      withLocalDeclD `first first fun _ =>
        withLocalDeclD `second second fun _ => do
          let fresh := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
          mkGoalKey fresh
    let natThenProp ← keyWithOrder natType target
    let propThenNat ← keyWithOrder target natType
    if natThenProp.strictEq propThenNat then
      throwError "GoalKey discarded ordered local-context semantics"
    let dependentKey (carrierName valueName : Name) : MetaM GoalKey :=
      withLocalDeclD carrierName (mkSort (.succ .zero)) fun carrier =>
        withLocalDeclD valueName carrier fun value => do
          let dependentTarget ← mkEq value value
          let fresh := (← mkFreshExprSyntheticOpaqueMVar dependentTarget).mvarId!
          mkGoalKey fresh
    let dependentLeft ← dependentKey `α `x
    let dependentRenamed ← dependentKey `Carrier `value
    unless dependentLeft.strictEq dependentRenamed do
      throwError "GoalKey alpha normalization broke a dependent local context"

example : True := by
  v3_goal_key_guard
  exact True.intro

elab "v3_atlas_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let limits : AtlasLimits := {
      maxNodes := 1, maxTransitions := 1, maxWorkUnits := 1
      maxMetaOps := 1, maxRenderedChars := 128, maxRegions := 1
    }
    let (atlas, some node, created) := ({} : ProofAtlas).observeGoal limits snap 0
      | throwError "Atlas rejected its root"
    unless created && atlas.nodes.size == 1 do
      throwError "Atlas root accounting is incorrect"
    let (sameAtlas, sameNode?, createdAgain) := atlas.observeGoal limits snap 1
    unless !createdAgain && sameNode? == some node && sameAtlas.stats.transpositions == 1 do
      throwError "Atlas failed strict transposition deduplication"
    let (atlas, first?) := sameAtlas.offerTransition limits node nativeCloseAction.toSymbolic
    unless first?.isSome && atlas.transitions.size == 1 do
      throwError "Atlas failed to add an executable transition"
    let (_, second?) := atlas.offerTransition limits node (structuralAction .intro).toSymbolic
    if second?.isSome then
      throwError "Atlas exceeded its global transition/work bound"

example : True := by
  v3_atlas_guard
  exact True.intro

/-- A planner can create a validated equality bridge even when no symbolic proposer is enabled. -/
example (α : Type) (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  propose
    (ai := true)
    (modelMode := "planner")
    (modelProvider := "replay")
    (modelReplayResponse := r#"{"root_value":0.9,"confidence":0.8,"thoughts":[{"id":"bad","kind":"equality_bridge","expression_ref":"missing_name"},{"id":"bridge-b","kind":"equality_bridge","expression_ref":"b"}]}"#)
    (directProbeSec := 0)
    (rankingMode := .planner)
    (structural := false)
    (cuts := false)
    (library := false)
    (equalityBridge := false)
    (iffBridge := false)
    (witnesses := false)
    (nativeTransforms := false)
    (nativeCases := false)
    (maxDepth := 3)
