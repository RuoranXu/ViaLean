import ViaLean.NativeSolver
import ViaLean.Compose
import ViaLean.Proposers.Structural
import ViaLean.Proposers.Equality
import ViaLean.Proposers.Cut
import ViaLean.Proposers.Witness
import ViaLean.Proposers.Library
import ViaLean.Proposers.Iff
import ViaLean.Scheduler.UCB
import ViaLean.Scheduler.PersistentStats
import ViaLean.Model.Guidance
import ViaLean.Solver.Router
import ViaLean.Workspace
import ViaLean.Synthesis.Engine
import ViaLean.Planner.Guidance
import ViaLean.Search.State
import ViaLean.Search.ModelCode
import Lean.Elab.Tactic.Meta
import ViaLean.Search.Decision
import ViaLean.Search.Replay
import ViaLean.Search.Execute
import ViaLean.Search.Controller
import Lean.Parser

open Lean Meta

namespace ViaLean
open SearchDecision SearchReplay ExecutionBoundary SearchController


private def describeOpenGoals
    (goals : Array MVarId) (state : SearchState) : MetaM String := do
  let mut chunks : Array String := #[]
  for index in [0:goals.size] do
    if chunks.size ≥ state.config.frontierMaxChildren then break
    let goal := goals[index]!
    unless ← goal.isAssigned do
      let snap ← snapshot goal
      let atlas ← FrontierEngine.build snap state.config (some state.budget)
      let rendered := (← ppExpr snap.target).pretty
      chunks := chunks.push s!"remaining_goal[{index}]: {rendered}"
      let mut futureCount := 0
      for probe in atlas do
        for view in probe.future do
          if futureCount ≥ min 8 state.config.frontierFutureNodes then break
          let signals := String.intercalate "; " view.signals.toList
          chunks := chunks.push
            s!"  future depth={view.depth} path={view.path}: {view.goal}\n    signals: {signals}"
          futureCount := futureCount + 1
        if futureCount ≥ min 8 state.config.frontierFutureNodes then break
  if chunks.isEmpty then
    return "candidate did not yield an assignable proof"
  return boundedText state.config.modelContextChars <| String.intercalate "\n" chunks.toList


private def freshGoal (target : Expr) : MetaM MVarId := do
  return (← mkFreshExprSyntheticOpaqueMVar target).mvarId!

private def availableSec (state : SearchState) (requested : Nat) : MetaM Nat := do
  let remaining ← state.budget.remainingSecFloor
  let requested := min requested (state.maxLeafSec?.getD requested)
  return min remaining requested

private def hasSpeculativeBudget (state : SearchState) : MetaM Bool := do
  return (← state.budget.remainingSecFloor) > state.config.finalDirectMinSec

private def noteDepth (state : SearchState) (depth : Nat) : MetaM Unit :=
  state.stats.modify fun stats => { stats with bridgeDepth := max stats.bridgeDepth depth }

private def noteAttempt (state : SearchState) (action : ProofAction) : MetaM Unit :=
  state.stats.modify fun stats =>
    match action.payload with
    | .close _ => { stats with directAttempts := stats.directAttempts + 1 }
    | .proposal _ => { stats with proposalAttempts := stats.proposalAttempts + 1 }
    | _ => stats

private def noteWinner (state : SearchState) (family : ProposalFamily) : MetaM Unit :=
  state.stats.modify fun stats => { stats with winningFamily? := some family }


private def emitTraining (state : SearchState) (kind : String)
    (payload : Json := Json.mkObj []) : MetaM Unit := do
  unless state.config.traceJsonlPath.isEmpty do
    let workspace ← state.workspace.get
    pushTrainingEvent state.traceEvents kind workspace.version payload

private def directProof?
    (goal : MVarId) (state : SearchState) (requestedSec : Nat) : MetaM (Option Expr) := do
  let seconds ← availableSec state requestedSec
  if seconds = 0 then return none
  let attempt ← state.router.solve {
    goal
    budgetMs := seconds * 1000
    wantDiagnostics := state.config.trace
  }
  if state.config.trace then
    trace[ViaLean.native]
      "backend={repr attempt.backend}, solved={attempt.proof?.isSome}, elapsedMs={attempt.elapsedMs}, diagnostics={attempt.diagnostics?}"
  return attempt.proof?

private def cheapClose? (snap : GoalSnapshot) : MetaM (Option Expr) := do
  for info in snap.locals do
    if ← isDefEq info.type snap.target then
      return some (mkFVar info.fvarId)
  if let some (_, lhs, rhs) := eqTarget? snap.target then
    if ← isDefEq lhs rhs then
      return some (← mkAppM ``Eq.refl #[lhs])
  if snap.target.isConstOf ``True then
    return some (mkConst ``True.intro)
  return none


private def collectActions
    (snap : GoalSnapshot) (state : SearchState) : MetaM (Array ProofAction) := do
  let cfg := state.config
  let mut actions := #[]
  if (← state.budget.remainingMs) = 0 then return actions
  if cfg.structural then
    actions := actions ++ (structuralProposals snap cfg).map Proposal.compile
  if (← state.budget.remainingMs) = 0 then return actions
  if cfg.equalityBridge && snap.shape == .equality then
    actions := actions ++ (← equalityProposals snap cfg).map Proposal.compile
  if (← state.budget.remainingMs) = 0 then return actions
  if cfg.iffBridge && snap.shape == .iff then
    actions := actions ++ (← iffProposals snap cfg).map Proposal.compile
  if (← state.budget.remainingMs) = 0 then return actions
  if cfg.witnesses && snap.shape == .exists then
    actions := actions ++ (← witnessProposals snap cfg).map Proposal.compile
  if (← state.budget.remainingMs) = 0 then return actions
  if cfg.cuts then
    actions := actions ++ (← localCutProposals snap cfg).map Proposal.compile
  if (← state.budget.remainingMs) = 0 then return actions
  if cfg.library then
    let premiseLimit := if cfg.maxRetrievedPremises = 0 then cfg.maxCandidates
      else cfg.maxRetrievedPremises
    let premises ← libraryPremiseProvider.retrieve snap premiseLimit
    if (← state.budget.remainingMs) > 0 then
      actions := actions ++ (← libraryCutProposals snap cfg premises).map Proposal.compile
  return actions.extract 0 (min actions.size cfg.maxActionsPerNode)


private def feedbackWindow (state : SearchState) : MetaM (Array SearchFeedback) := do
  let events ← state.feedback.get
  let limit := state.config.modelMaxFeedbackEvents
  if limit = 0 then return #[]
  let start := events.size - min events.size limit
  return events.extract start events.size

private structure NeuralStep where
  guidance? : Option ModelGuidance := none
  novelActions : Array ProofAction := #[]
  leanCandidates : Array String := #[]

private def guidanceFor?
    (snap : GoalSnapshot) (actions : Array ProofAction)
    (state : SearchState) (depth : Nat) : MetaM NeuralStep := do
  if !state.config.ai || !state.modelEnabled then return {}
  let mode := modelMode state
  unless mode == "policy" || mode == "planner" do return {}
  if mode == "policy" && actions.isEmpty then return {}
  if mode == "policy" then
    if let some cached := (← state.guidanceCache.get).get? snap.fingerprint then
      return { guidance? := cached }
  if mode == "planner" then
    let workspace ← state.workspace.get
    let cursor ← state.plannerCursor.get
    let trigger := ReplanEngine.decide state.config workspace snap.key cursor
    unless trigger.openEpoch do
      return { guidance? := (← state.guidanceCache.get).get? snap.fingerprint |>.join }
    state.stats.modify fun stats => { stats with replanCount := stats.replanCount + 1 }
    if (← state.plannerCalls.get) >= state.config.plannerMaxCalls then return {}
    if state.config.trace then
      trace[ViaLean.model]
        "neural_epoch cause={repr trigger.cause}, semantic_delta={trigger.semanticDelta}, workspace={workspace.version}"
    emitTraining state "replan" <| Json.mkObj [
      ("root", toString snap.key.bucket),
      ("cause", (repr trigger.cause).pretty),
      ("semantic_delta", trigger.semanticDelta)]
    let mut step : NeuralStep := {}
    let mut continueAfterExpansion := true
    while continueAfterExpansion &&
        (← state.plannerCalls.get) < state.config.plannerMaxCalls &&
        (← state.budget.remainingMs) > 0 do
      continueAfterExpansion := false
      state.plannerCalls.modify (· + 1)
      let epochCursor ← state.plannerCursor.get
      let memory : ModelProtocol.PlannerMemoryView := {
        lastSeenVersion := epochCursor.lastVersion
        observationCount := epochCursor.observationCount
        primaryFamily? := epochCursor.strategy.primaryFamily?
        confidence := epochCursor.confidence
      }
      let result ← PlannerEngine.query?
        state.workspace snap state.config state.budget memory
      match result with
      | .ok decision =>
          if state.config.trace then
            trace[ViaLean.model]
              "planner depth={depth}, value={decision.guidance.value}, confidence={decision.confidence}, scored={decision.guidance.actionScores.size}, novel={decision.novelActions.size}, code={decision.leanCandidates.size}, expansions={decision.expansionRequests.size}"
          emitTraining state "planner" <| Json.mkObj [
            ("root", toString snap.key.bucket),
            ("value", toJson decision.guidance.value),
            ("confidence", toJson decision.confidence),
            ("scored", decision.guidance.actionScores.size),
            ("novel_actions", decision.novelActions.size),
            ("expansions", decision.expansionRequests.size)]
          let novelActions := decision.novelActions.foldl (init := step.novelActions)
            fun accumulated action =>
              if accumulated.any (·.fingerprint == action.fingerprint) then accumulated
              else accumulated.push action
          let leanCandidates := decision.leanCandidates.foldl (init := step.leanCandidates)
            fun accumulated code =>
              if accumulated.contains code then accumulated else accumulated.push code
          step := { guidance? := some decision.guidance, novelActions, leanCandidates }
          let after ← state.workspace.get
          let previous ← state.plannerCursor.get
          state.plannerCursor.set <|
            ReplanEngine.advance after snap.key decision.confidence decision.strategy previous
          continueAfterExpansion := decision.expansionResults.any fun expansion =>
            expansion.addedNodes > 0 || expansion.addedTransitions > 0
      | .error error =>
          if state.config.trace then trace[ViaLean.model] "planner fallback: {error}"
          let after ← state.workspace.get
          let previous ← state.plannerCursor.get
          state.plannerCursor.set <|
            ReplanEngine.advance after snap.key 0.0 previous.strategy previous
    state.guidanceCache.modify (·.insert snap.fingerprint step.guidance?)
    state.plannerVersions.modify (·.insert snap.fingerprint (← state.workspace.get).version)
    return step
  state.plannerCalls.modify (· + 1)
  let result ← ModelGuidanceEngine.query? snap actions depth state.config state.budget
  let guidance? ← match result with
    | .ok guidance =>
        if state.config.trace then
          trace[ViaLean.model]
            "depth={depth}, value={guidance.value}, scored={guidance.actionScores.size}"
        pure (some guidance)
    | .error error =>
        if state.config.trace then trace[ViaLean.model] "fallback: {error}"
        pure none
  state.guidanceCache.modify (·.insert snap.fingerprint guidance?)
  return { guidance? }

mutual
  partial def solveGoal?
      (goal : MVarId) (state : SearchState) (depth : Nat) : MetaM (Option Expr) :=
    goal.withContext do
      if depth > state.config.maxDepth then return none
      if (← state.budget.remainingMs) = 0 then return none
      noteDepth state depth
      let snap ← snapshot goal
      if (← state.budget.remainingMs) = 0 then return none
      if state.path.goalKeys.contains snap.key then return none
      let nodeId? ← Workspace.observeGoal state.workspace state.config snap depth state.activeTransition?
      let state := { state with
        path := { state.path with
          goalKeys := state.path.goalKeys.insert snap.key } }

      if state.config.frontier && state.config.atlasGraph && nodeId?.isSome then
        let burst ← FrontierEngine.expandWorkspace state.workspace snap state.config {
          maxDepth := min state.config.frontierFutureDepth state.config.atlasExpansionMaxDepth
          maxWidthPerNode := min state.config.frontierFutureWidth
            state.config.atlasExpansionMaxWidth
          workUnits := state.config.atlasGuaranteedWork
          reason := "guaranteed-symbolic"
        } (some state.budget)
        emitTraining state "atlas_build" <| Json.mkObj [
          ("root", toString snap.key.bucket), ("depth", depth),
          ("added_nodes", burst.addedNodes),
          ("added_transitions", burst.addedTransitions),
          ("meta_ops", burst.metaOps),
          ("completed", burst.completed)]

      let synthesis ← LocalSynthesizer.synthesizeDetailed
        snap state.config state.config.maxActionsPerNode
      let synthesized := synthesis.candidates
      for term in synthesis.discovered do
        if term.depth > 0 then
          discard <| Workspace.registerObject state.workspace .term term.term
            (some term.type) .verified .derived #[] #[] (1.0 / Float.ofNat (term.depth + 1))
      for gap in synthesis.gaps do
        discard <| Workspace.registerObject state.workspace .helperLemma gap
          none .pending .derived #[] #[] 0.65
      for candidate in synthesized do
        unless candidate.complete do
          discard <| Workspace.registerObject state.workspace .term candidate.term
            none .pending .derived #[] #[] 0.55
      if let some nodeId := nodeId? then
        let complete := synthesized.foldl (init := 0) fun n candidate =>
          n + if candidate.complete then 1 else 0
        Workspace.setSynthesisSignals state.workspace nodeId {
          exactLocal := complete > 0
          completeInhabitants := complete
          partialInhabitants := synthesized.size - complete
        }
      if let some proof := LocalSynthesizer.firstComplete? synthesized then
        if depth = 0 then noteWinner state .direct
        return some (← finalizeProof snap.target proof)

      if let some proof ← cheapClose? snap then
        if depth = 0 then noteWinner state .direct
        return some (← finalizeProof snap.target proof)

      -- A short direct probe is always a first-class action.
      if let some proof ← observingMeta? <|
          tryProofAction? snap nativeCloseAction state depth then
        return some proof

      let baseActions ← collectActions snap state
      if state.modelEnabled && modelMode state == "interactive" then
        if let some proof ← observingMeta? <| tryInteractive? snap baseActions state depth then
          return some proof
      let neural ← guidanceFor? snap baseActions state depth
      let actions := neural.novelActions.foldl (init := baseActions) fun actions action =>
        if actions.any (·.fingerprint == action.fingerprint) then actions else actions.push action
      if let some nodeId := nodeId? then
        Workspace.offerActions state.workspace state.config nodeId actions
      if state.config.modelLeanCode && state.config.experimentalRawLeanCode &&
          modelMode state == "planner" then
        for code in neural.leanCandidates.take state.config.modelMaxCodeCandidates do
          if let some proof := (← tryModelLeanCandidate? snap code state depth).proof? then
            return some proof
      let actions ← orderActions state neural.guidance? actions
      for action in actions do
        unless action.family == .structural do
          unless ← hasSpeculativeBudget state do continue
        if let some proof ← observingMeta? <| tryProofAction? snap action state depth then
          return some proof

      -- Preserve a serious direct fallback under the same global deadline.
      let remaining ← state.budget.remainingSecFloor
      if remaining = 0 then return none
      noteAttempt state nativeCloseAction
      let proof? ← directProof? goal state remaining
      state.scheduler.record .direct (if proof?.isSome then 1.0 else 0.0)
      if depth = 0 && proof?.isSome then noteWinner state .direct
      return proof?

  partial def solveTarget?
      (target : Expr) (state : SearchState) (depth : Nat) : MetaM (Option Expr) := do
    let goal ← freshGoal target
    solveGoal? goal state depth

  partial def tryStructural?
      (snap : GoalSnapshot) (state : SearchState) (depth : Nat) : MetaM (Option Expr) := do
    match ← whnf snap.target with
    | .forallE .. =>
        forallTelescopeReducing snap.target fun fvars childTarget => do
          let some childProof ← solveTarget? childTarget state (depth + 1) | return none
          let proof ← mkLambdaFVars fvars childProof
          return some (← finalizeProof snap.target proof)
    | target =>
      if target.isAppOfArity ``And 2 then
        let args := target.getAppArgs
        let some left ← solveTarget? args[0]! state (depth + 1) | return none
        let some right ← solveTarget? args[1]! state (depth + 1) | return none
        return some (← composeAction snap.target .andIntro #[left, right])
      if target.isAppOfArity ``Iff 2 then
        let args := target.getAppArgs
        let forwardTarget ← mkArrow args[0]! args[1]!
        let backwardTarget ← mkArrow args[1]! args[0]!
        let some forward ← solveTarget? forwardTarget state (depth + 1)
          | return none
        let some backward ← solveTarget? backwardTarget state (depth + 1)
          | return none
        return some (← composeAction snap.target .iffIntro #[forward, backward])
      return none

  partial def tryProposal?
      (snap : GoalSnapshot) (proposal : Proposal)
      (state : SearchState) (depth : Nat) : MetaM (Option Expr) := do
    let proposalKey := ProposalKey.ofProposal proposal
    if state.path.proposals.contains proposalKey then return none
    let proposals := state.path.proposals.insert proposalKey
    let path := { state.path with proposals }
    let state := { state with path }
    let childState := { state with maxLeafSec? := some state.config.candidateProbeSec }
    if state.config.trace then
      trace[ViaLean.proposal]
        "try kind={repr proposal.kind}, source={proposal.source}, depth={depth}"
    match proposal.payload with
    | .directTerm term =>
      let termType ← inferType term
      unless ← isDefEq termType snap.target do return none
      return some (← finalizeProof snap.target term)
    | .equalityMid mid =>
      let some (_, lhs, rhs) := eqTarget? snap.target | return none
      let leftTarget ← mkEq lhs mid
      let rightTarget ← mkEq mid rhs
      let some left ← solveTarget? leftTarget childState (depth + 1) | return none
      let some right ← solveTarget? rightTarget childState (depth + 1) | return none
      return some (← composeAction snap.target .eqTrans #[left, right])
    | .iffMid mid =>
      let target ← whnf snap.target
      unless target.isAppOfArity ``Iff 2 do return none
      let args := target.getAppArgs
      let some left ← solveTarget? (mkIff args[0]! mid) childState (depth + 1) | return none
      let some right ← solveTarget? (mkIff mid args[1]!) childState (depth + 1) | return none
      return some (← composeAction snap.target .iffTrans #[left, right])
    | .cutType cutType =>
      let some cutProof ← solveTarget? cutType childState (depth + 1) | return none
      withLocalDeclD `h cutType fun h => do
        let some continuation ← solveTarget? snap.target childState (depth + 1) | return none
        let continuation ← mkLambdaFVars #[h] continuation
        return some (← composeAction snap.target (.cutApply cutType)
          #[cutProof, continuation])
    | .libraryApply theoremName =>
      if (← state.budget.remainingMs) = 0 then return none
      let root ← freshGoal snap.target
      let children ← root.apply (← mkConstWithFreshMVarLevels theoremName)
      if children.length > state.config.maxStructuralChildren then return none
      unless ← solveFrontierChildren children.toArray childState depth do return none
      let some proof ← getExprMVarAssignment? root | return none
      return some (← finalizeProof snap.target proof)
    | .witness witness =>
      let some (_, predicate) := existsTarget? snap.target | return none
      let childTarget := mkApp predicate witness
      let some childProof ← solveTarget? childTarget childState (depth + 1) | return none
      return some (← composeAction snap.target (.existsIntro witness) #[childProof])
    | .structural _ => tryStructural? snap state depth

  partial def solveFrontierChildren
      (children : Array MVarId) (state : SearchState) (depth : Nat) : MetaM Bool := do
    for child in children do
      unless ← child.isAssigned do
        let some proof ← solveGoal? child state (depth + 1) | return false
        child.assign proof
    return true

  /-- Replay a selected symbolic preview and solve only the finite obligations it exposes. -/
  partial def tryFrontierProbe?
      (snap : GoalSnapshot) (probe : FrontierProbe)
      (state : SearchState) (depth : Nat) : MetaM (Option Expr) := snap.goalId.withContext do
    if !probe.executable then return none
    let root ← freshGoal snap.target
    let mut children : Array MVarId := #[]
    match probe.operation with
    | "whnf" =>
        let child ← root.replaceTargetDefEq (← whnf snap.target)
        children := #[child]
    | "simp-target-star" =>
        let simpCtx ← Simp.Context.mkDefault
        let (result, _) ← simpTargetStar root simpCtx
        match result with
        | .closed => pure ()
        | .modified child => children := #[child]
        | .noChange => return none
    | "simp-context" =>
        let simpCtx ← Simp.Context.mkDefault
        let propHyps ← getPropHyps
        let (result?, _) ← simpGoal root simpCtx (fvarIdsToSimp := propHyps)
        if let some (_, child) := result? then children := #[child]
    | "contradiction-core" => root.contradiction
    | "rewrite-forward" | "rewrite-reverse" =>
        let some subject := probe.subject? | return none
        let result ← root.rewrite snap.target (mkFVar subject) (symm := probe.symm)
        let child ← root.replaceTargetEq result.eNew result.eqProof
        children := #[child] ++ result.mvarIds
    | "cases-one-layer" =>
        let some subject := probe.subject? | return none
        let branches ← root.cases subject
        children := branches.map (·.mvarId)
    | "constructor-one-layer" =>
        let some ctor := probe.constructor? | return none
        children := (← root.apply (← mkConstWithFreshMVarLevels ctor)).toArray
    | "apply-one-layer" =>
        let some subject := probe.subject? | return none
        children := (← root.apply (mkFVar subject)).toArray
    | _ => return none
    if children.size > state.config.frontierMaxChildren then return none
    unless ← solveFrontierChildren children state depth do return none
    let some proof ← getExprMVarAssignment? root | return none
    return some (← finalizeProof snap.target proof)

  /-- Execute a validated model tactic on an isolated goal. Any open goals are handed
  to the ordinary bounded solver; failures restore the complete metavariable state. -/
  partial def tryModelLeanCandidate?
      (snap : GoalSnapshot) (candidate : String)
      (state : SearchState) (depth : Nat) : MetaM ModelCodeAttempt := snap.goalId.withContext do
    let code := candidate.trimAscii.toString
    if code.isEmpty then return { detail := "empty Lean candidate" }
    if code.length > state.config.modelMaxCodeChars then
      return { detail := s!"Lean candidate exceeds modelMaxCodeChars={state.config.modelMaxCodeChars}" }
    if (← state.budget.remainingMs) = 0 then
      return { detail := "global search deadline expired before candidate execution" }
    let tacticSyntax ← match parseSafeModelTacticWithKinds (← getEnv) code
        state.router.modelSyntaxKinds with
      | .ok tacticSyntax => pure tacticSyntax
      | .error error => return { detail := boundedText state.config.modelContextChars error }
    let saved ← saveState
    try
      let root ← freshGoal snap.target
      let heartbeatLimit := max 1 state.config.modelCodeMaxHeartbeats * 1000
      let (remainingList, _) ←
        withoutSpeculativeMessages <|
          withTheReader Core.Context (fun context => { context with maxHeartbeats := heartbeatLimit }) do
            withCurrHeartbeats <| Elab.runTactic root tacticSyntax
      let remaining := remainingList.toArray
      if remaining.size > state.config.maxStructuralChildren then
        let detail ← describeOpenGoals remaining state
        saved.restore
        return {
          outcome := "expanded"
          detail := boundedText state.config.modelContextChars
            s!"candidate produced {remaining.size} goals, above maxStructuralChildren={state.config.maxStructuralChildren}\n{detail}"
        }
      let childState := { state with modelEnabled := false }
      let completed ← solveFrontierChildren remaining childState depth
      if completed then
        if let some proof ← getExprMVarAssignment? root then
          let proof ← finalizeProof snap.target proof
          return {
            proof? := some proof
            outcome := "solved"
            detail := if remaining.isEmpty then
              "model tactic closed the goal and passed the final proof boundary"
            else
              s!"model tactic exposed {remaining.size} obligations; bounded symbolic search closed all of them"
          }
      let detail ← describeOpenGoals remaining state
      saved.restore
      return {
        outcome := if remaining.isEmpty then "failed" else "expanded"
        detail
      }
    catch ex =>
      let errorText ← ex.toMessageData.toString
      saved.restore
      return {
        detail := boundedText state.config.modelContextChars s!"tactic_error: {errorText}"
      }

  partial def tryInteractive?
      (snap : GoalSnapshot) (actions : Array ProofAction)
      (state : SearchState) (depth : Nat) : MetaM (Option Expr) := do
    if state.config.modelMaxRounds = 0 then return none
    let frontier ← FrontierEngine.build snap state.config (some state.budget)
    let mut attempted : Std.HashSet UInt64 := {}
    let mut attemptedProbes : Std.HashSet String := {}
    let mut attemptedCodes : Std.HashSet String := {}
    for round in [0:state.config.modelMaxRounds] do
      if (← state.budget.remainingMs) = 0 then break
      state.plannerCalls.modify (· + 1)
      let feedback ← feedbackWindow state
      let response ← ModelGuidanceEngine.queryInteraction?
        snap actions depth round feedback frontier state.config state.budget
      let continuation ← match response with
        | .ok continuation => pure continuation
        | .error error =>
            if state.config.trace then trace[ViaLean.model] "interactive fallback: {error}"
            break
      if state.config.trace then
        trace[ViaLean.model]
          "interactive round={round}, frontier={frontier.size}, feedback={feedback.size}, code={continuation.leanCandidates.size}, selections={continuation.selections.size}"
      let mut madeProgress := false
      if state.config.modelLeanCode && state.config.experimentalRawLeanCode then
        let candidateLimit := min continuation.leanCandidates.size
          state.config.modelMaxCodeCandidates
        for index in [0:candidateLimit] do
          if (← state.budget.remainingMs) = 0 then break
          let code := continuation.leanCandidates[index]!
          let codeId : UInt64 := hash code
          if attemptedCodes.contains code then continue
          attemptedCodes := attemptedCodes.insert code
          madeProgress := true
          let started ← IO.monoMsNow
          let attempt ← tryModelLeanCandidate? snap code state depth
          let elapsedMs := (← IO.monoMsNow) - started
          let events ← state.feedback.get
          let rendered := (← ppExpr snap.target).pretty
          let event : SearchFeedback := {
            sequence := events.size
            depth
            goal := boundedText 512 rendered
            actionId := s!"lean/{codeId}"
            family := "model/lean-code"
            action := boundedText 512 code
            outcome := attempt.outcome
            elapsedMs
            detail := attempt.detail
          }
          state.feedback.set (events.push event)
          if let some proof := attempt.proof? then return some proof
      for selection in continuation.selections do
        let action? := resolveAction selection actions
        if let some action := action? then
          if attempted.contains action.fingerprint then continue
          attempted := attempted.insert action.fingerprint
          madeProgress := true
          let childState := { state with modelEnabled := false }
          if let some proof ← observingMeta? <| tryProofAction? snap action childState depth then
            return some proof
          break
        let probe? := resolveProbe selection frontier
        let some probe := probe? | continue
        if attemptedProbes.contains probe.id then continue
        attemptedProbes := attemptedProbes.insert probe.id
        madeProgress := true
        let childState := { state with modelEnabled := false }
        if state.config.trace then
          trace[ViaLean.model]
            "select probe perspective={probe.perspective}, operation={probe.operation}, source={probe.source}, goals={probe.goals.size}, facts={probe.facts.size}"
        let started ← IO.monoMsNow
        let proof? ← observingMeta? <| tryFrontierProbe? snap probe childState depth
        let elapsedMs := (← IO.monoMsNow) - started
        let events ← state.feedback.get
        let rendered := (← ppExpr snap.target).pretty
        let event : SearchFeedback := {
          sequence := events.size
          depth
          goal := if rendered.length ≤ 512 then rendered else (rendered.take 512).toString ++ "…"
          actionId := probe.id
          family := s!"frontier/{probe.perspective}"
          action := s!"{probe.operation}/{probe.source}"
          outcome := if proof?.isSome then "solved" else "failed"
          elapsedMs
        }
        state.feedback.set (events.push event)
        if let some proof := proof? then return some proof
        break
      if !madeProgress then break
    return none

  partial def tryProofAction?
      (snap : GoalSnapshot) (action : ProofAction)
      (state : SearchState) (depth : Nat) : MetaM (Option Expr) := do
    if (← state.budget.remainingMs) = 0 then return none
    noteAttempt state action
    let started ← IO.monoMsNow
    let transition? ← Workspace.beginAction state.workspace state.config snap action
    let execState := { state with activeTransition? := transition? }
    let result ← match action.payload with
      | .close .native => directProof? snap.goalId execState state.config.directProbeSec
      | .close _ => pure none
      | .structural _ => tryStructural? snap execState depth
      | .proposal proposal => tryProposal? snap proposal execState depth
      | .sketch _ => pure none
    let elapsedMs := (← IO.monoMsNow) - started
    let failureClass? ← if result.isSome then pure none
      else if (← state.budget.remainingMs) = 0 then pure (some .timeout)
      else pure (some (failureClassFor action))
    Workspace.finishAction state.workspace transition?
      (if result.isSome then .solved else .failed) elapsedMs failureClass?
    if let some thoughtId := plannerThoughtId? action then
      discard <| Workspace.setObjectStatus state.workspace thoughtId
        (if result.isSome then .verified else .pending)
    emitTraining state "transition_outcome" <| Json.mkObj [
      ("root", toString snap.key.bucket),
      ("transition", transition?.map (fun id => Json.str (toString id)) |>.getD Json.null),
      ("action", toString action.fingerprint),
      ("family", action.toSymbolic.family.name),
      ("outcome", if result.isSome then "solved" else "failed"),
      ("failure_class", failureClass?.map (fun failure => Json.str (repr failure).pretty)
        |>.getD Json.null),
      ("elapsed_ms", elapsedMs)]
    state.scheduler.record action.family (if result.isSome then 1.0 else 0.0)
    if depth = 0 && result.isSome then noteWinner state action.family
    if modelMode state == "interactive" then
      let events ← state.feedback.get
      let rendered := (← ppExpr snap.target).pretty
      let goalText := if rendered.length ≤ 512 then rendered else (rendered.take 512).toString ++ "…"
      let event : SearchFeedback := {
        sequence := events.size
        depth
        goal := goalText
        actionId := toString action.fingerprint
        family := (repr action.family).pretty
        action := feedbackActionName action
        outcome := if result.isSome then "solved" else "failed"
        elapsedMs
      }
      state.feedback.set (events.push event)
    return result

end

private def createScheduler (config : ProposeConfig) (budget : Budget) : MetaM SchedulerState := do
  let scheduler ← SchedulerState.create
  if !config.persistentStatsPath.isEmpty && (← budget.remainingMs) > 0 then
    try
      let persisted ← loadPersistentStats (System.FilePath.mk config.persistentStatsPath)
      if (← budget.remainingMs) > 0 then persisted.seedScheduler scheduler
    catch _ => pure ()
  return scheduler

private def persistScheduler
    (config : ProposeConfig) (budget : Budget) (scheduler : SchedulerState) : MetaM Unit := do
  if !config.persistentStatsPath.isEmpty && (← budget.remainingMs) > 0 then
    try
      savePersistentStats (System.FilePath.mk config.persistentStatsPath)
        (← scheduler.toPersistentStats)
    catch _ => pure ()

/-- Run the complete search with an explicitly supplied leaf-solver portfolio.
This is the dependency-inversion boundary used by optional integrations such as
mathlib; the core package does not need to import those dependencies. -/
def runSearchWithRouter
    (goal : MVarId) (config : ProposeConfig) (router : LeafRouter) : MetaM SolveResult := do
  let start ← IO.monoMsNow
  let budget ← Budget.start config.timeoutSec
  let scheduler ← createScheduler config budget
  let guidanceCache ← IO.mkRef {}
  let feedback ← IO.mkRef #[]
  let statsRef ← IO.mkRef ({} : SolveStats)
  let workspace ← IO.mkRef ({} : ProofWorkspace)
  let plannerVersions ← IO.mkRef {}
  let plannerCalls ← IO.mkRef 0
  let plannerCursor ← IO.mkRef ({} : PlannerCursor)
  let traceEvents ← IO.mkRef (#[] : Array TrainingTraceEvent)
  let state : SearchState := {
    config := config
    budget := budget
    scheduler := scheduler
    guidanceCache := guidanceCache
    feedback := feedback
    stats := statsRef
    router := router
    workspace := workspace
    plannerVersions := plannerVersions
    plannerCalls := plannerCalls
    plannerCursor := plannerCursor
    traceEvents := traceEvents
  }
  let earlyProof? ← if router.preSnapshotBackends.isEmpty then pure none else do
    let remaining ← budget.remainingMs
    if remaining = 0 then pure none else do
      statsRef.modify fun stats => { stats with directAttempts := stats.directAttempts + 1 }
      let attempt ← router.solvePreSnapshot {
        goal
        budgetMs := min remaining 1000
        wantDiagnostics := config.trace
      }
      if config.trace then
        trace[ViaLean.native]
          "pre-snapshot backend={repr attempt.backend}, solved={attempt.proof?.isSome}, elapsedMs={attempt.elapsedMs}"
      pure attempt.proof?
  let proof?? ← match earlyProof? with
    | some proof => pure (some (some (← finalizeProof (← goal.getType) proof)))
    | none => withinBudget? budget do
      let proof? ← solveGoal? goal state 0
      match proof? with
      | some proof => return some (← finalizeProof (← goal.getType) proof)
      | none => return none
  let proof? := proof??.join
  let elapsed := (← IO.monoMsNow) - start
  let finalWorkspace ← workspace.get
  let modelCalls ← plannerCalls.get
  statsRef.modify fun stats => {
    stats with
    elapsedMs := elapsed
    modelCalls
    atlasNodes := finalWorkspace.atlas.nodes.size
    atlasTransitions := finalWorkspace.atlas.transitions.size
    atlasMetaOps := finalWorkspace.atlas.stats.metaOps
  }
  persistScheduler config budget scheduler
  emitTraining state "search_result" <| Json.mkObj [
    ("solved", proof?.isSome),
    ("elapsed_ms", elapsed),
    ("direct_attempts", (← statsRef.get).directAttempts),
    ("proposal_attempts", (← statsRef.get).proposalAttempts)]
  unless config.traceJsonlPath.isEmpty do
    try
      writeTrainingJsonl config.traceJsonlPath (← traceEvents.get) config.traceMaxEvents
    catch error =>
      if config.trace then trace[ViaLean] "jsonl trace write failed: {error.toMessageData}"
  let stats ← statsRef.get
  match proof? with
  | some proof => return SolveResult.solved proof stats
  | none => return SolveResult.failed stats

def runSearch (goal : MVarId) (config : ProposeConfig) : MetaM SolveResult :=
  runSearchWithRouter goal config (.nativeOnly config)

def runManualProposal
    (goal : MVarId) (config : ProposeConfig) (proposal : Proposal) : MetaM (Option Expr) :=
  goal.withContext do
    let budget ← Budget.start config.timeoutSec
    let scheduler ← createScheduler config budget
    let guidanceCache ← IO.mkRef {}
    let feedback ← IO.mkRef #[]
    let stats ← IO.mkRef ({} : SolveStats)
    let workspace ← IO.mkRef ({} : ProofWorkspace)
    let plannerVersions ← IO.mkRef {}
    let plannerCalls ← IO.mkRef 0
    let plannerCursor ← IO.mkRef ({} : PlannerCursor)
    let traceEvents ← IO.mkRef (#[] : Array TrainingTraceEvent)
    let state : SearchState := {
      config := config
      budget := budget
      scheduler := scheduler
      guidanceCache := guidanceCache
      feedback := feedback
      stats := stats
      router := .nativeOnly config
      workspace := workspace
      plannerVersions := plannerVersions
      plannerCalls := plannerCalls
      plannerCursor := plannerCursor
      traceEvents := traceEvents
    }
    let proof?? ← withinBudget? budget do
      let snap ← snapshot goal
      tryProofAction? snap proposal.compile state 0
    persistScheduler config budget scheduler
    return proof??.join

def diagnose (goal : MVarId) (config : ProposeConfig) : MetaM MessageData := goal.withContext do
  let budget ← Budget.start config.timeoutSec
  let report? ← withinBudget? budget do
    let snap ← snapshot goal
    let equalities ← if config.equalityBridge && (← budget.remainingMs) > 0 then
      equalityProposals snap config else pure #[]
    let witnesses ← if config.witnesses && (← budget.remainingMs) > 0 then
      witnessProposals snap config else pure #[]
    let cuts ← if config.cuts && (← budget.remainingMs) > 0 then
      localCutProposals snap config else pure #[]
    let frontier ← if config.frontier then
      FrontierEngine.build snap config (some budget) else pure #[]
    let perspectives := String.intercalate "," <|
      (frontier.map (·.perspective)).toList.eraseDups
    let direct ← if config.directProbeSec = 0 || (← budget.remainingMs) = 0 then pure none else do
      let scheduler ← SchedulerState.create
      let guidanceCache ← IO.mkRef {}
      let feedback ← IO.mkRef #[]
      let stats ← IO.mkRef ({} : SolveStats)
      let workspace ← IO.mkRef ({} : ProofWorkspace)
      let plannerVersions ← IO.mkRef {}
      let plannerCalls ← IO.mkRef 0
      let plannerCursor ← IO.mkRef ({} : PlannerCursor)
      let traceEvents ← IO.mkRef (#[] : Array TrainingTraceEvent)
      let state : SearchState := {
        config := config
        budget := budget
        scheduler := scheduler
        guidanceCache := guidanceCache
        feedback := feedback
        stats := stats
        router := .nativeOnly config
        workspace := workspace
        plannerVersions := plannerVersions
        plannerCalls := plannerCalls
        plannerCursor := plannerCursor
        traceEvents := traceEvents
      }
      directProof? goal state config.directProbeSec
    return m!"ViaLean: shape={repr snap.shape}, direct={direct.isSome}, " ++
      m!"equality={equalities.size}, witness={witnesses.size}, cuts={cuts.size}, " ++
      m!"frontier={frontier.size} [{perspectives}]"
  return report?.getD m!"ViaLean: diagnostics exhausted the {config.timeoutSec}s deadline"

end ViaLean
