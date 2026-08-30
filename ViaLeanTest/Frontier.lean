import ViaLean

open Lean Meta Elab Tactic ViaLean

private def hasPerspective (atlas : Array FrontierProbe) (name : String) : Bool :=
  atlas.any fun probe => probe.perspective == name

private def checkAtlas
    (goal : MVarId) (expected : Array String) (requireExecutable := true) : TacticM Unit :=
  goal.withContext do
    let snap ← snapshot goal
    let cfg : ProposeConfig := {
      frontierMaxProbes := 24
      frontierMaxPerPerspective := 4
      frontierMaxChildren := 6
      frontierMaxFacts := 12
      frontierForwardDepth := 2
    }
    let atlas ← FrontierEngine.build snap cfg
    unless atlas.size ≤ cfg.frontierMaxProbes do
      throwError "frontier exceeded its global probe bound"
    for perspective in expected do
      unless hasPerspective atlas perspective do
        throwError "missing frontier perspective: {perspective}; got {atlas.map (·.perspective)}"
    if requireExecutable then
      unless atlas.any (·.executable) do
        throwError "frontier contains no executable probe"

elab "frontier_logic_guard" : tactic => do
  checkAtlas (← getMainGoal) #["elimination", "backward", "forward"]

elab "frontier_equality_guard" : tactic => do
  checkAtlas (← getMainGoal) #["rewrite", "equality-graph"]

elab "frontier_construction_guard" : tactic => do
  checkAtlas (← getMainGoal) #["normalization", "construction"]

example (P Q R : Prop) (p : P) (pq : P → Q) (qr : Q → R) (_h : P ∨ R) : R := by
  frontier_logic_guard
  exact qr (pq p)

example (α : Type) (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := by
  frontier_equality_guard
  exact h₁.trans h₂

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  frontier_construction_guard
  exact ⟨p, q⟩

/-- No traditional action is enabled: the replay model selects an executable frontier probe. -/
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  propose
    (ai := true)
    (modelMode := "interactive")
    (modelProvider := "replay")
    (modelReplayResponse := "{\"continue\":[{\"probe_index\":0}],\"rationale\":\"select a symbolic counterfactual\"}")
    (directProbeSec := 0)
    (structural := false)
    (cuts := false)
    (library := false)
    (equalityBridge := false)
    (iffBridge := false)
    (witnesses := false)
    (nativeTransforms := false)
    (nativeCases := false)
    (frontierMaxProbes := 16)
    (modelMaxRounds := 2)
    (maxDepth := 3)