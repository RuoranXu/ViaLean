import ViaLean

open ViaLean

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
  let request : InteractionRequest := {
    requestId := "goal-1"
    round := 2
    depth := 1
    shape := "proposition"
    target := "R"
    locals := #["h : P ∨ Q"]
    actions := #[]
    feedback := #[{
      sequence := 0
      depth := 3
      goal := "R"
      actionId := "17"
      family := "structural"
      outcome := "failed"
      elapsedMs := 4
    }]
  }
  let text := ModelProtocol.interactionRequestText request
  text.contains "\"protocol\":\"vialean.interactive.v1\"" &&
  text.contains "\"search_feedback\"" && text.contains "\"depth\":3" &&
  text.contains "\"action\":\"\"" && !text.contains "\"prior\""

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
