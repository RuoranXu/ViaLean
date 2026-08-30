import ViaLean

open Lean Meta Elab Tactic ViaLean

#guard
  match ModelProtocol.parseGuidance
      "{\"value\":0.75,\"actions\":[{\"id\":\"17\",\"score\":0.25},{\"id\":\"17\",\"score\":0.9}],\"rationale\":\"prefer the second route\"}" with
  | .ok guidance =>
      guidance.value == 0.75 &&
      ModelProtocol.ModelGuidance.score? guidance 17 == some 0.9 &&
      guidance.actionScores.size == 1
  | .error _ => false

#guard
  match ModelProtocol.parseGuidance
      "```json\n{\"value\":2.0,\"actions\":[{\"id\":\"4\",\"score\":-1.0}]}\n```" with
  | .ok guidance =>
      guidance.value == 1.0 &&
      ModelProtocol.ModelGuidance.score? guidance 4 == some 0.0
  | .error _ => false

#guard
  match ModelProtocol.parseGuidance
      "<think>compare {terms} carefully</think>\n{\"value\":0.6,\"actions\":[{\"id\":\"9\",\"score\":0.8}],\"rationale\":\"handles {braces} in strings\"}" with
  | .ok guidance =>
      guidance.value == 0.6 &&
      ModelProtocol.ModelGuidance.score? guidance 9 == some 0.8
  | .error _ => false

#guard
  match ModelProtocol.parseGuidance "{\"value\":\"NaN\",\"actions\":[]}" with
  | .ok guidance => guidance.value == 0.5
  | .error _ => false

#guard ModelProtocol.blendScore 0.2 (some 1.0) 1.0 == 1.0

#guard
  match ModelProtocol.parseArgs "[\"adapter.py\",\"--device\",\"cuda\"]" with
  | .ok args => args == #["adapter.py", "--device", "cuda"]
  | .error _ => false

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  propose
    (ai := true)
    (modelProvider := "replay")
    (modelReplayResponse := "{\"value\":0.9,\"actions\":[]}")
    (directProbeSec := 0)
    (structural := false)
#guard
  match ModelProtocol.parseContinuation
      "```json\n{\"continue\":[{\"index\":1},{\"id\":\"17\"},\"23\",{\"unknown\":true}],\"rationale\":\"use search feedback\"}\n```" with
  | .ok continuation =>
      continuation.selections.size == 3 &&
      continuation.selections[0]!.index? == some 1 &&
      continuation.selections[1]!.actionId? == some 17 &&
      continuation.selections[2]!.actionId? == some 23
  | .error _ => false

#guard
  match ModelProtocol.parseContinuation
      "{\"continue\":[{\"probe_id\":\"probe-7\"},{\"probe_index\":2}]}" with
  | .ok continuation =>
      continuation.selections.size == 2 &&
      continuation.selections[0]!.probeId? == some "probe-7" &&
      continuation.selections[1]!.probeIndex? == some 2
  | .error _ => false

#guard
  match ModelProtocol.parseContinuation
      r#"{"lean_candidates":[{"code":"by intro h; exact h"},"constructor"],"rationale":"write Lean first"}"# with
  | .ok continuation =>
      continuation.selections.isEmpty &&
      continuation.leanCandidates == #["by intro h; exact h", "constructor"]
  | .error _ => false

#guard
  let request : InteractionRequest := {
    requestId := "goal-1"
    round := 2
    depth := 1
    shape := "proposition"
    target := "R"
    locals := #["h : P ∨ Q"]
    actions := #[]
    frontier := #[{
      id := "probe-7"
      perspective := "elimination"
      operation := "cases-one-layer"
      source := "h"
      result := "branched"
      executable := true
      goals := #["P ⊢ R", "Q ⊢ R"]
      future := #[{
        depth := 2
        path := "root/cases/apply"
        goal := "p : P ⊢ R"
        signals := #["exact local p closes this node"]
      }]
    }]
    feedback := #[{
      sequence := 0
      depth := 3
      goal := "R"
      actionId := "17"
      family := "structural"
      outcome := "failed"
      elapsedMs := 4
      detail := "remaining_goal[0]: R"
    }]
  }
  let text := ModelProtocol.interactionRequestText request
  let hasNewFields :=
    text.contains r#""future""# &&
    text.contains r#""path":"root/cases/apply""# &&
    text.contains r#""detail":"remaining_goal[0]: R""#
  hasNewFields &&
  text.contains "\"protocol\":\"vialean.interactive.v1\"" &&
  text.contains "\"search_feedback\"" && text.contains "\"depth\":3" &&
  text.contains "\"action\":\"\"" && text.contains "\"frontier\"" &&
  text.contains "\"executable\":true" && !text.contains "\"prior\""

example (P : Prop) : P → P := by
  propose
    (ai := true)
    (modelMode := "interactive")
    (modelProvider := "replay")
    (modelReplayResponse := "{\"continue\":[{\"index\":0}],\"rationale\":\"expand implication\"}")
    (directProbeSec := 0)
    (cuts := false)
    (library := false)
    (maxDepth := 3)

elab "reject_unsafe_model_code" : tactic => do
  match parseSafeModelTactic (← getEnv) "by run_tac IO.println \"unsafe\"" with
  | .error _ => pure ()
  | .ok _ => throwError "unsafe run_tac unexpectedly passed the model-code boundary"

example : True := by
  reject_unsafe_model_code
  exact True.intro

/-- A model can supply a complete Lean proof without selecting a controller action. -/
example (P : Prop) : P → P := by
  propose
    (ai := true)
    (modelMode := "interactive")
    (modelProvider := "replay")
    (modelReplayResponse := r#"{"lean_candidates":[{"code":"by intro h; exact h"}]}"#)
    (directProbeSec := 0)
    (structural := false)
    (cuts := false)
    (library := false)
    (equalityBridge := false)
    (iffBridge := false)
    (witnesses := false)
    (nativeTransforms := false)
    (nativeCases := false)
    (modelMaxRounds := 1)

/-- A partial model tactic exposes obligations that symbolic search completes. -/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  propose
    (ai := true)
    (modelMode := "interactive")
    (modelProvider := "replay")
    (modelReplayResponse := r#"{"lean_candidates":[{"code":"constructor"}]}"#)
    (directProbeSec := 0)
    (structural := false)
    (cuts := false)
    (library := false)
    (equalityBridge := false)
    (iffBridge := false)
    (witnesses := false)
    (nativeTransforms := false)
    (nativeCases := false)
    (modelMaxRounds := 1)
