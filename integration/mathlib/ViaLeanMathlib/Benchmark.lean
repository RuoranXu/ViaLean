import ViaLeanMathlib

open Lean Parser Tactic Meta Elab Tactic

namespace ViaLean.Mathlib

/-- One kernel-checked dataset attempt. The schema is intentionally independent
of miniF2F so the same harness can be reused for ProofNet or local corpora. -/
structure DatasetCaseResult where
  dataset : String
  split : String
  caseName : String
  solved : Bool
  elapsedMs : Nat
  directAttempts : Nat
  proposalAttempts : Nat
  modelCalls : Nat
  replanCount : Nat
  atlasNodes : Nat
  atlasTransitions : Nat
  atlasMetaOps : Nat
  searchExceptions : Nat := 0
  internalError : Bool := false
  attempts : Nat := 1
  profile : String := "single"
  budgetSec : Nat := 0
deriving Inhabited, Repr

def DatasetCaseResult.toJson (result : DatasetCaseResult) : Json := Json.mkObj [
  ("schema", "vialean.dataset.v1"),
  ("dataset", result.dataset),
  ("split", result.split),
  ("case", result.caseName),
  ("solved", result.solved),
  ("elapsed_ms", result.elapsedMs),
  ("direct_attempts", result.directAttempts),
  ("proposal_attempts", result.proposalAttempts),
  ("model_calls", result.modelCalls),
  ("replan_count", result.replanCount),
  ("atlas_nodes", result.atlasNodes),
  ("atlas_transitions", result.atlasTransitions),
  ("atlas_meta_ops", result.atlasMetaOps),
  ("search_exceptions", result.searchExceptions),
  ("internal_error", result.internalError),
  ("attempts", result.attempts),
  ("profile", result.profile),
  ("budget_sec", result.budgetSec)
]

private def datasetResult (dataset split caseName : String)
    (solved : Bool) (stats : SolveStats)
    (searchExceptions : Nat := 0)
    (internalError : Bool := false) (attempts : Nat := 1)
    (profile : String := "single") (budgetSec : Nat := 0) : DatasetCaseResult := {
  dataset
  split
  caseName
  solved
  elapsedMs := stats.elapsedMs
  directAttempts := stats.directAttempts
  proposalAttempts := stats.proposalAttempts
  modelCalls := stats.modelCalls
  replanCount := stats.replanCount
  atlasNodes := stats.atlasNodes
  atlasTransitions := stats.atlasTransitions
  atlasMetaOps := stats.atlasMetaOps
  searchExceptions
  internalError
  attempts
  profile
  budgetSec
}

declare_config_elab datasetCaseConfig ProposeConfig

/-- Run the current goal through the mathlib router, emit one stable JSON result,
and accept only a finalized proof. Failed cases emit their record before making
the containing test fail. -/
elab (name := vialeanDatasetCase)
    "vialean_dataset_case" dataset:str split:str caseName:str config:optConfig : tactic => do
  let cfg <- datasetCaseConfig config
  let goal <- getMainGoal
  let datasetName := dataset.getString
  let splitName := split.getString
  let name := caseName.getString
  match <- runSearchWithRouter goal cfg (mathlibRouter cfg) with
  | .solved proof stats =>
      liftM (m := IO) <| IO.println (datasetResult datasetName splitName name true stats (budgetSec := cfg.timeoutSec)).toJson.compress
      goal.assign proof
      replaceMainGoal []
  | .failed stats =>
      liftM (m := IO) <| IO.println (datasetResult datasetName splitName name false stats (budgetSec := cfg.timeoutSec)).toJson.compress
      throwError "ViaLean failed dataset case {datasetName}/{splitName}/{name} within {cfg.timeoutSec}s"

declare_command_config_elab datasetEvalConfig ProposeConfig

private def withDatasetRecDepth (action : TermElabM α) : TermElabM α :=
  withOptions (fun options => options.setNat `maxRecDepth 10000) <|
    withTheReader Core.Context
      (fun context => { context with maxRecDepth := max context.maxRecDepth 10000 }) action

private structure DatasetAttemptProfile where
  name : String
  config : ProposeConfig

private def datasetAttemptProfiles (cfg : ProposeConfig) : Array DatasetAttemptProfile :=
  let total := max cfg.timeoutSec 4
  let first := max 1 ((total + 1) / 2)
  let second := max 1 (total / 7)
  let third := max 1 (total / 7)
  let fourth := max 1 (total - first - second - third)
  #[
    { name := "default", config := {
        cfg with
        timeoutSec := first
        directProbeSec := max cfg.directProbeSec first } },
    { name := "structural", config := {
        cfg with
        timeoutSec := second
        frontier := false
        atlasGraph := false
        library := false
        maxDepth := max cfg.maxDepth 3
        maxCandidates := max cfg.maxCandidates 18 } },
    { name := "flat-diverse", config := {
        cfg with
        timeoutSec := third
        atlasGraph := false
        frontier := true
        frontierMaxProbes := max cfg.frontierMaxProbes 48
        maxCandidates := max cfg.maxCandidates 18 } },
    { name := "deep-atlas", config := {
        cfg with
        timeoutSec := fourth
        maxDepth := max cfg.maxDepth 4
        maxCandidates := max cfg.maxCandidates 24
        maxActionsPerNode := max cfg.maxActionsPerNode 48
        frontierFutureDepth := max cfg.frontierFutureDepth 5
        frontierFutureNodes := max cfg.frontierFutureNodes 48
        atlasMaxNodes := max cfg.atlasMaxNodes 160
        atlasMaxTransitions := max cfg.atlasMaxTransitions 256
        atlasMaxWorkUnits := max cfg.atlasMaxWorkUnits 384
        atlasMaxMetaOps := max cfg.atlasMaxMetaOps 384 } }
  ]
private def mergeSolveStats (left right : SolveStats) : SolveStats := {
  directAttempts := left.directAttempts + right.directAttempts
  proposalAttempts := left.proposalAttempts + right.proposalAttempts
  modelCalls := left.modelCalls + right.modelCalls
  replanCount := left.replanCount + right.replanCount
  atlasNodes := left.atlasNodes + right.atlasNodes
  atlasTransitions := left.atlasTransitions + right.atlasTransitions
  atlasMetaOps := left.atlasMetaOps + right.atlasMetaOps
  bridgeDepth := max left.bridgeDepth right.bridgeDepth
  elapsedMs := left.elapsedMs + right.elapsedMs
  winningFamily? := right.winningFamily?.orElse fun _ => left.winningFamily?
}

private def evaluateDatasetTarget (dataset split caseName : String)
    (target : Expr) (cfg : ProposeConfig) : MetaM DatasetCaseResult := do
  let mut totals : SolveStats := {}
  let mut attempts := 0
  let mut searchExceptions := 0
  for profile in datasetAttemptProfiles cfg do
    attempts := attempts + 1
    let saved <- saveState
    let started <- IO.monoMsNow
    let _ : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try
      let goal := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
      let outcome <- ExecutionBoundary.withoutSpeculativeMessages <|
        runSearchWithRouter goal profile.config (mathlibRouter profile.config)
      saved.restore
      match outcome with
      | .solved _ stats =>
          totals := mergeSolveStats totals stats
          return datasetResult dataset split caseName true totals searchExceptions false attempts profile.name cfg.timeoutSec
      | .failed stats =>
          totals := mergeSolveStats totals stats
    catch error =>
      trace[ViaLean.native]
        "dataset profile {profile.name} raised: {error.toMessageData}"
      saved.restore
      searchExceptions := searchExceptions + 1
      let elapsed := (← IO.monoMsNow) - started
      totals := mergeSolveStats totals { elapsedMs := elapsed }
  return datasetResult dataset split caseName false totals searchExceptions false attempts "exhausted" cfg.timeoutSec
/-- Evaluate a dataset proposition without declaring it. Unlike the tactic
entrypoint, an unsolved target is recorded and evaluation continues, so a full
corpus run needs neither answer declarations nor `sorry` fallbacks. -/
elab (name := vialeanDatasetEval)
    "#vialean_dataset_eval" dataset:str split:str caseName:str
    config:optConfig ":" target:term : command => do
  let cfg <- datasetEvalConfig config
  let datasetName := dataset.getString
  let splitName := split.getString
  let name := caseName.getString
  let commandStarted <- liftM (m := IO) IO.monoMsNow
  let result <-
    try
      Command.liftTermElabM <| withDatasetRecDepth do
        let initialLog <- Core.getMessageLog
        let saved <- saveState
        let started <- IO.monoMsNow
        let result <-
          try
            let targetExpr <- Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabType target
            let targetExpr <- instantiateMVars targetExpr
            let result <- evaluateDatasetTarget datasetName splitName name targetExpr cfg
            let hadErrors := (← Core.getMessageLog).hasErrors
            saved.restore
            Core.setMessageLog initialLog
            if hadErrors then
              pure { result with solved := false, internalError := true }
            else
              pure result
          catch _ =>
            saved.restore
            Core.setMessageLog initialLog
            let elapsed := (← IO.monoMsNow) - started
            pure <| datasetResult datasetName splitName name false { elapsedMs := elapsed }
              0 true 1 "elaboration" cfg.timeoutSec
        pure result
    catch _ =>
      let elapsed := (← liftM (m := IO) IO.monoMsNow) - commandStarted
      pure <| datasetResult datasetName splitName name false { elapsedMs := elapsed }
        0 true 1 "command" cfg.timeoutSec
  liftM (m := IO) do
    IO.println result.toJson.compress
    (← IO.getStdout).flush
end ViaLean.Mathlib
