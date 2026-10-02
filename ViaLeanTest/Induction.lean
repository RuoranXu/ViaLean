import ViaLean

open Lean Meta Elab Tactic ViaLean

inductive InductionChain where
  | base
  | step (tail : InductionChain)
deriving Inhabited

namespace InductionChain

opaque append : InductionChain → InductionChain → InductionChain

axiom append_base (left : InductionChain) : append left .base = left
axiom append_step (left right : InductionChain) :
  append left (.step right) = .step (append left right)

/-- A theorem (rather than an axiom) must remain visible to the bounded
current-file premise pool. -/
theorem append_base_bridge (left : InductionChain) : append left .base = left :=
  append_base left

elab "induction_frontier_guard" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let snap ← snapshot goal
    let cfg : ProposeConfig := {
      frontierFutureDepth := 3
      frontierFutureWidth := 8
      frontierFutureNodes := 32
      frontierMaxPerPerspective := 6
      atlasMaxMetaOps := 256
    }
    let premises ← libraryPremiseProvider.retrieve snap cfg.maxRetrievedPremises
    unless premises.any fun premise => premise.name == ``append_base_bridge do
      throwError "current-file theorem was lost from the semantic premise pool"
    let probes ← FrontierEngine.build snap cfg
    unless probes.any fun probe => probe.operation == "induction-one-layer" do
      throwError "frontier omitted executable structural induction"
    let some future := probes.find? fun probe => probe.perspective == "future-graph"
      | throwError "frontier omitted the bounded future graph"
    unless future.future.any fun view => view.path.contains "induction:" do
      throwError "bounded future graph omitted induction descendants"

example (n : InductionChain) : append .base n = n := by
  induction_frontier_guard
  propose
    (timeoutSec := 8)
    (directProbeSec := 2)
    (candidateProbeSec := 1)
    (maxDepth := 5)
    (nativeMaxDepth := 10)

example (left right : InductionChain) :
    append (.step left) right = .step (append left right) := by
  propose
    (timeoutSec := 8)
    (directProbeSec := 2)
    (candidateProbeSec := 1)
    (maxDepth := 5)
    (nativeMaxDepth := 10)

end InductionChain