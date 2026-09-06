import ViaLean.Search

open Lean Meta

namespace ViaLean

inductive BenchmarkMode
  | nativeOnly | symbolicActions | flatFrontier | graphAtlas
  | atlasPolicy | atlasPolicyValue | plannerExpansion | interactiveRaw
deriving BEq, Repr, Inhabited

def BenchmarkMode.name : BenchmarkMode → String
  | .nativeOnly => "native-only"
  | .symbolicActions => "symbolic-actions"
  | .flatFrontier => "flat-frontier"
  | .graphAtlas => "graph-atlas"
  | .atlasPolicy => "atlas-policy"
  | .atlasPolicyValue => "atlas-policy-value"
  | .plannerExpansion => "planner-expansion"
  | .interactiveRaw => "interactive-raw"

structure BenchmarkCaseResult where
  caseName : String
  mode : BenchmarkMode
  solved : Bool
  elapsedMs : Nat
  directAttempts : Nat
  proposalAttempts : Nat
  bridgeDepth : Nat
  modelCalls : Nat
  replanCount : Nat
  atlasNodes : Nat
  atlasTransitions : Nat
  atlasMetaOps : Nat
deriving Inhabited, Repr

def BenchmarkCaseResult.toJson (result : BenchmarkCaseResult) : Json := Json.mkObj [
  ("schema", "vialean.benchmark.v3"),
  ("case", result.caseName),
  ("mode", result.mode.name),
  ("solved", result.solved),
  ("elapsed_ms", result.elapsedMs),
  ("direct_attempts", result.directAttempts),
  ("proposal_attempts", result.proposalAttempts),
  ("bridge_depth", result.bridgeDepth),
  ("model_calls", result.modelCalls),
  ("replan_count", result.replanCount),
  ("atlas_nodes", result.atlasNodes),
  ("atlas_transitions", result.atlasTransitions),
  ("atlas_meta_ops", result.atlasMetaOps)
]

/-- All variants retain the same wall-clock and Atlas work caps. Only the feature
under ablation changes. Replay responses make neural variants deterministic. -/
def benchmarkConfig (base : ProposeConfig) (mode : BenchmarkMode) : ProposeConfig :=
  match mode with
  | .nativeOnly => {
      base with
      ai := false
      frontier := false
      atlasGraph := false
      structural := false
      cuts := false
      library := false
      equalityBridge := false
      iffBridge := false
      witnesses := false
    }
  | .symbolicActions => {
      base with
      ai := false
      frontier := false
      atlasGraph := false
    }
  | .flatFrontier => {
      base with
      ai := true
      modelMode := "interactive"
      modelProvider := "replay"
      modelReplayResponse := r#"{"continue":[]}"#
      atlasGraph := false
    }
  | .graphAtlas => { base with ai := false, frontier := true, atlasGraph := true }
  | .atlasPolicy => {
      base with
      ai := true
      modelMode := "policy"
      modelProvider := "replay"
      modelReplayResponse := r#"{"value":0.6,"actions":[]}"#
      atlasGraph := true
    }
  | .atlasPolicyValue => {
      base with
      ai := true
      modelMode := "planner"
      modelProvider := "replay"
      modelReplayResponse :=
        r#"{"root_value":0.6,"confidence":0.7,"strategy":{"primary_family":"backward","horizon":2}}"#
      plannerAllowExpansion := false
    }
  | .plannerExpansion => {
      base with
      ai := true
      modelMode := "planner"
      modelProvider := "replay"
      modelReplayResponse :=
        r#"{"root_value":0.6,"confidence":0.35,"strategy":{"primary_family":"__FIRST_REGION_FAMILY__","horizon":3},"expansion_requests":[{"region_id":"__FIRST_REGION_ID__","extra_depth":2,"extra_width":2,"reason_code":"matched-compute-lookahead"}]}"#
      plannerAllowExpansion := true
    }
  | .interactiveRaw => {
      base with
      ai := true
      modelMode := "interactive"
      modelProvider := "replay"
      modelReplayResponse :=
        r#"{"lean_candidates":[{"code":"by exact True.intro"}]}"#
      experimentalRawLeanCode := true
      modelLeanCode := true
      atlasGraph := false
    }

def runBenchmarkCase (caseName : String) (target : Expr)
    (base : ProposeConfig) (mode : BenchmarkMode) : MetaM BenchmarkCaseResult := do
  let saved ← saveState
  try
    let goal := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
    let result ← runSearch goal (benchmarkConfig base mode)
    saved.restore
    match result with
    | .solved _ stats => return {
        caseName, mode, solved := true
        elapsedMs := stats.elapsedMs
        directAttempts := stats.directAttempts
        proposalAttempts := stats.proposalAttempts
        bridgeDepth := stats.bridgeDepth
        modelCalls := stats.modelCalls
        replanCount := stats.replanCount
        atlasNodes := stats.atlasNodes
        atlasTransitions := stats.atlasTransitions
        atlasMetaOps := stats.atlasMetaOps
      }
    | .failed stats => return {
        caseName, mode, solved := false
        elapsedMs := stats.elapsedMs
        directAttempts := stats.directAttempts
        proposalAttempts := stats.proposalAttempts
        bridgeDepth := stats.bridgeDepth
        modelCalls := stats.modelCalls
        replanCount := stats.replanCount
        atlasNodes := stats.atlasNodes
        atlasTransitions := stats.atlasTransitions
        atlasMetaOps := stats.atlasMetaOps
      }
  catch _ =>
    saved.restore
    return {
      caseName, mode, solved := false, elapsedMs := base.timeoutSec * 1000,
      directAttempts := 0, proposalAttempts := 0, bridgeDepth := 0,
      modelCalls := 0, replanCount := 0, atlasNodes := 0,
      atlasTransitions := 0, atlasMetaOps := 0 }

def matchedComputeModes : Array BenchmarkMode := #[
  .nativeOnly, .symbolicActions, .flatFrontier, .graphAtlas,
  .atlasPolicy, .atlasPolicyValue, .plannerExpansion, .interactiveRaw
]

def runMatchedComputeCase (caseName : String) (target : Expr)
    (base : ProposeConfig := {}) : MetaM (Array BenchmarkCaseResult) := do
  let mut results := #[]
  for mode in matchedComputeModes do
    results := results.push (← runBenchmarkCase caseName target base mode)
  return results

def benchmarkJsonl (results : Array BenchmarkCaseResult) : String :=
  String.intercalate "\n" (results.map (·.toJson.compress)).toList

end ViaLean
