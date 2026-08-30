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

open Lean Meta

namespace ViaLean

structure SolveStats where
  directAttempts   : Nat := 0
  proposalAttempts : Nat := 0
  bridgeDepth      : Nat := 0
  elapsedMs        : Nat := 0
  winningFamily?   : Option ProposalFamily := none
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
  stats : IO.Ref SolveStats
  path   : SearchPath := {}
  maxLeafSec? : Option Nat := none
  modelEnabled : Bool := true

/-- Restore the metavariable context after an exception or failed branch. -/
def observingMeta? (action : MetaM (Option α)) : MetaM (Option α) := do
  let saved ← getMCtx
  try
    let result ← action
    if result.isNone then setMCtx saved
    return result
  catch _ =>
    setMCtx saved
    return none

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

private def directProof?
    (goal : MVarId) (state : SearchState) (requestedSec : Nat) : MetaM (Option Expr) := do
  let seconds ← availableSec state requestedSec
  if seconds = 0 then return none
  let attempt ← solveWithNative goal state.config (seconds * 1000)
  if state.config.trace then
    trace[ViaLean.native]
      "solved={attempt.proof?.isSome}, nodes={attempt.stats.nodes}, elapsedMs={attempt.elapsedMs}"
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

private def orderActions
    (state : SearchState) (guidance? : Option ModelGuidance)
    (actions : Array ProofAction) : MetaM (Array ProofAction) := do
  let stats ← state.scheduler.snapshot
  let total := stats.fold (init := 0) fun total _ family => total + family.attempts
  let baseScore (action : ProofAction) :=
    if state.config.deterministic || !state.config.ucb then action.prior
    else
      let familyStats := (stats.get? action.family).getD {}
      ucbScore familyStats total action.prior
        state.config.ucbExploration state.config.ucbPriorWeight
  let score (action : ProofAction) :=
    let base := baseScore action
    let actionSignal? := guidance?.bind fun guidance =>
      ModelProtocol.ModelGuidance.score? guidance action.fingerprint
    let signal? := match actionSignal? with
      | some signal => some signal
      | none => guidance?.map (·.value)
    let blended := ModelProtocol.blendScore base signal? state.config.modelWeight
    blended / max 0.1 action.estimatedCost
  return actions.insertionSort fun a b => score a > score b

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
    let premises ← libraryPremiseProvider.retrieve snap cfg.maxCandidates
    if (← state.budget.remainingMs) > 0 then
      actions := actions ++ (← libraryCutProposals snap cfg premises).map Proposal.compile
  return actions

private def modelMode (state : SearchState) : String :=
  state.config.modelMode.trimAscii.toString.toLower

private def feedbackActionName (action : ProofAction) : String :=
  match action.payload with
  | .close solver => s!"close/{(repr solver).pretty}"
  | .structural rule => s!"structural/{(repr rule).pretty}"
  | .proposal proposal => s!"{(repr proposal.kind).pretty}/{proposal.source}"
  | .sketch holes => s!"sketch/{holes.size}"
private def feedbackWindow (state : SearchState) : MetaM (Array SearchFeedback) := do
  let events ← state.feedback.get
  let limit := state.config.modelMaxFeedbackEvents
  if limit = 0 then return #[]
  let start := events.size - min events.size limit
  return events.extract start events.size
private def guidanceFor?
    (snap : GoalSnapshot) (actions : Array ProofAction)
    (state : SearchState) (depth : Nat) : MetaM (Option ModelGuidance) := do
  if !state.config.ai || !state.modelEnabled || modelMode state != "policy" || actions.isEmpty then return none
  if let some cached := (← state.guidanceCache.get).get? snap.fingerprint then
    return cached
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
  return guidance?

mutual
  partial def solveGoal?
      (goal : MVarId) (state : SearchState) (depth : Nat) : MetaM (Option Expr) :=
    goal.withContext do
      if depth > state.config.maxDepth then return none
      if (← state.budget.remainingMs) = 0 then return none
      noteDepth state depth
      let snap ← snapshot goal
      if (← state.budget.remainingMs) = 0 then return none
      if state.path.goalFingerprints.contains snap.fingerprint then return none
      let state := { state with
        path := { state.path with
          goalFingerprints := state.path.goalFingerprints.insert snap.fingerprint } }

      if let some proof ← cheapClose? snap then
        if depth = 0 then noteWinner state .direct
        return some (← finalizeProof snap.target proof)

      -- A short direct probe is always a first-class action.
      if let some proof ← observingMeta? <|
          tryProofAction? snap nativeCloseAction state depth then
        return some proof

      let actions ← collectActions snap state
      if state.modelEnabled && modelMode state == "interactive" then
        if let some proof ← observingMeta? <| tryInteractive? snap actions state depth then
          return some proof
      let guidance? ← guidanceFor? snap actions state depth
      let actions ← orderActions state guidance? actions
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
    | .forallE name domain body binderInfo =>
        withLocalDecl name binderInfo domain fun fvar => do
          let childTarget := body.instantiate1 fvar
          let some childProof ← solveTarget? childTarget state (depth + 1) | return none
          let proof ← mkLambdaFVars #[fvar] childProof
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
    if state.path.proposalFingerprints.contains proposal.fingerprint then return none
    let proposalFingerprints := state.path.proposalFingerprints.insert proposal.fingerprint
    let path := { state.path with proposalFingerprints }
    let state := { state with path }
    let childState := { state with maxLeafSec? := some state.config.candidateProbeSec }
    if state.config.trace then
      trace[ViaLean.proposal]
        "try kind={repr proposal.kind}, source={proposal.source}, depth={depth}"
    match proposal.payload with
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
  partial def tryInteractive?
      (snap : GoalSnapshot) (actions : Array ProofAction)
      (state : SearchState) (depth : Nat) : MetaM (Option Expr) := do
    if state.config.modelMaxRounds = 0 then return none
    let frontier ← FrontierEngine.build snap state.config (some state.budget)
    if actions.isEmpty && frontier.isEmpty then return none
    let mut attempted : Std.HashSet UInt64 := {}
    let mut attemptedProbes : Std.HashSet String := {}
    for round in [0:state.config.modelMaxRounds] do
      if (← state.budget.remainingMs) = 0 then break
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
          "interactive round={round}, frontier={frontier.size}, feedback={feedback.size}, selections={continuation.selections.size}"
      let mut madeProgress := false
      for selection in continuation.selections do
        let action? := match selection.actionId? with
          | some id => actions.find? fun (action : ProofAction) => action.fingerprint == id
          | none => selection.index?.bind fun index => actions[index]?
        if let some action := action? then
          if attempted.contains action.fingerprint then continue
          attempted := attempted.insert action.fingerprint
          madeProgress := true
          let childState := { state with modelEnabled := false }
          if let some proof ← observingMeta? <| tryProofAction? snap action childState depth then
            return some proof
          break
        let probe? := match selection.probeId? with
          | some probeId => frontier.find? fun (probe : FrontierProbe) => probe.id == probeId && probe.executable
          | none => selection.probeIndex?.bind fun index =>
              frontier[index]?.filter fun (probe : FrontierProbe) => probe.executable
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
    let result ← match action.payload with
      | .close .native => directProof? snap.goalId state state.config.directProbeSec
      | .close _ => pure none
      | .structural _ => tryStructural? snap state depth
      | .proposal proposal => tryProposal? snap proposal state depth
      | .sketch _ => pure none
    let elapsedMs := (← IO.monoMsNow) - started
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

private partial def monitorBudgetCancellation
    (budget : Budget) (token : IO.CancelToken) (parent? : Option IO.CancelToken)
    (finished : IO.Ref Bool) : IO Unit := do
  if ← finished.get then return
  if let some parent := parent? then
    if ← parent.isSet then
      token.set
      return
  let remaining ← budget.remainingMs
  if remaining = 0 then
    token.set
  else
    IO.sleep (UInt32.ofNat (min 10 remaining))
    monitorBudgetCancellation budget token parent? finished

private def withinBudget? (budget : Budget) (action : MetaM α) : MetaM (Option α) := do
  let parentCancel? := (← readThe Core.Context).cancelTk?
  let localCancel ← IO.CancelToken.new
  let finished ← IO.mkRef false
  let _monitor ← IO.asTask
    (monitorBudgetCancellation budget localCancel parentCancel? finished) .dedicated
  let attempt ← try
    let result ← withTheReader Core.Context (fun context =>
      { context with cancelTk? := some localCancel }) action
    pure (Except.ok result : Except Exception α)
  catch error => pure (Except.error error : Except Exception α)
  finished.set true
  match attempt with
  | Except.ok result =>
      if let some parent := parentCancel? then
        if ← parent.isSet then throwInterruptException
      if (← localCancel.isSet) || (← budget.remainingMs) = 0 then return none
      return some result
  | Except.error error =>
      if let some parent := parentCancel? then
        if ← parent.isSet then throw error
      if ← localCancel.isSet then return none
      throw error

def runSearch (goal : MVarId) (config : ProposeConfig) : MetaM SolveResult := do
  let start ← IO.monoMsNow
  let budget ← Budget.start config.timeoutSec
  let scheduler ← createScheduler config budget
  let guidanceCache ← IO.mkRef {}
  let feedback ← IO.mkRef #[]
  let statsRef ← IO.mkRef ({} : SolveStats)
  let proof?? ← withinBudget? budget do
    let proof? ← solveGoal? goal
      { config, budget, scheduler, guidanceCache, feedback, stats := statsRef } 0
    match proof? with
    | some proof => return some (← finalizeProof (← goal.getType) proof)
    | none => return none
  let proof? := proof??.join
  let elapsed := (← IO.monoMsNow) - start
  statsRef.modify fun stats => { stats with elapsedMs := elapsed }
  persistScheduler config budget scheduler
  let stats ← statsRef.get
  match proof? with
  | some proof => return SolveResult.solved proof stats
  | none => return SolveResult.failed stats

def runManualProposal
    (goal : MVarId) (config : ProposeConfig) (proposal : Proposal) : MetaM (Option Expr) :=
  goal.withContext do
    let budget ← Budget.start config.timeoutSec
    let scheduler ← createScheduler config budget
    let guidanceCache ← IO.mkRef {}
    let feedback ← IO.mkRef #[]
    let stats ← IO.mkRef ({} : SolveStats)
    let proof?? ← withinBudget? budget do
      let snap ← snapshot goal
      tryProofAction? snap proposal.compile
        { config, budget, scheduler, guidanceCache, feedback, stats } 0
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
      directProof? goal { config, budget, scheduler, guidanceCache, feedback, stats } config.directProbeSec
    return m!"ViaLean: shape={repr snap.shape}, direct={direct.isSome}, " ++
      m!"equality={equalities.size}, witness={witnesses.size}, cuts={cuts.size}, " ++
      m!"frontier={frontier.size} [{perspectives}]"
  return report?.getD m!"ViaLean: diagnostics exhausted the {config.timeoutSec}s deadline"

end ViaLean
