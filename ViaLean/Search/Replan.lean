import ViaLean.Workspace
import ViaLean.Model.Protocol

namespace ViaLean

inductive ReplanCause
  | initial | newRoot | materialAtlasDelta | expansionCompleted
  | strategyExhausted | structuralFailures | uncertaintyReduced | none
deriving BEq, Repr, Inhabited

/-- Collision-confirmed semantic signature. Pretty-printed text and debug errors are
intentionally absent, so cosmetic changes never open a neural epoch. -/
structure WorkspaceSignature where
  nodeKeys : Array GoalKey
  transitions : Array (UInt64 × TransitionOutcome × Array UInt64)
  objects : Array (UInt64 × KnowledgeStatus × UInt64)
deriving BEq, Inhabited

structure PlannerCursor where
  lastRoot? : Option GoalKey := none
  signature? : Option WorkspaceSignature := none
  lastVersion : Nat := 0
  observationCount : Nat := 0
  nodeCount : Nat := 0
  transitionCount : Nat := 0
  objectCount : Nat := 0
  failureStreak : Nat := 0
  confidence : Float := 0.5
  strategy : ModelProtocol.StrategyPlan := {}
deriving Inhabited

structure ReplanDecision where
  openEpoch : Bool := false
  cause : ReplanCause := .none
  semanticDelta : Nat := 0
deriving Inhabited, Repr

namespace ReplanEngine

def signature (workspace : ProofWorkspace) : WorkspaceSignature := {
  nodeKeys := workspace.atlas.nodes.map (·.key)
  transitions := workspace.atlas.transitions.map fun transition =>
    (transition.candidate.fingerprint, transition.evidence.outcome, transition.children)
  objects := workspace.objects.map fun object =>
    (object.id, object.status, hash object.expression)
}

private def recentObservations (workspace : ProofWorkspace) (cursor : PlannerCursor) :
    Array StructuredObservation :=
  workspace.observations.extract
    (min cursor.observationCount workspace.observations.size) workspace.observations.size

private def isStructuralFailure (observation : StructuredObservation) : Bool :=
  observation.outcome == .failed || observation.outcome == .timedOut ||
  observation.outcome == .rejected

private def expansionCompleted (observations : Array StructuredObservation) : Bool :=
  observations.any fun observation =>
    observation.transition?.isNone && observation.outcome == .expanded

private def strategyExhausted (workspace : ProofWorkspace)
    (strategy : ModelProtocol.StrategyPlan) : Bool :=
  match strategy.primaryFamily?.bind StrategyFamily.ofName? with
  | none => false
  | some family =>
      let relevant := workspace.atlas.transitions.filter fun transition =>
        transition.candidate.family == family && transition.executable
      !relevant.isEmpty && relevant.all fun transition =>
        transition.evidence.outcome == .failed ||
        transition.evidence.outcome == .rejected ||
        transition.evidence.outcome == .timedOut

def decide (cfg : ProposeConfig) (workspace : ProofWorkspace)
    (root : GoalKey) (cursor : PlannerCursor) : ReplanDecision :=
  let current := signature workspace
  match cursor.signature? with
  | none => { openEpoch := true, cause := .initial }
  | some previous =>
      if cursor.lastRoot?.all (fun old => !old.strictEq root) then
        { openEpoch := true, cause := .newRoot }
      else if previous == current then
        {}
      else
        let observations := recentObservations workspace cursor
        let nodeDelta := workspace.atlas.nodes.size - min cursor.nodeCount workspace.atlas.nodes.size
        let transitionDelta :=
          workspace.atlas.transitions.size - min cursor.transitionCount workspace.atlas.transitions.size
        let objectDelta := workspace.objects.size - min cursor.objectCount workspace.objects.size
        let semanticDelta := nodeDelta + transitionDelta + objectDelta
        if expansionCompleted observations then
          { openEpoch := true, cause := .expansionCompleted, semanticDelta }
        else if (observations.filter isStructuralFailure).size +
            cursor.failureStreak >= cfg.plannerFailureReplanCount then
          { openEpoch := true, cause := .structuralFailures, semanticDelta }
        else if strategyExhausted workspace cursor.strategy then
          { openEpoch := true, cause := .strategyExhausted, semanticDelta }
        else if 1.0 - cursor.confidence >= cfg.plannerUncertaintyThreshold &&
            semanticDelta > 0 then
          { openEpoch := true, cause := .uncertaintyReduced, semanticDelta }
        else if nodeDelta >= cfg.plannerMinNewNodes ||
            transitionDelta >= cfg.plannerMinNewTransitions || objectDelta > 0 then
          { openEpoch := true, cause := .materialAtlasDelta, semanticDelta }
        else
          {}

def advance (workspace : ProofWorkspace) (root : GoalKey)
    (confidence : Float) (strategy : ModelProtocol.StrategyPlan)
    (previous : PlannerCursor) : PlannerCursor :=
  let observations := recentObservations workspace previous
  let recentFailures := observations.filter isStructuralFailure |>.size
  {
    lastRoot? := some root
    signature? := some (signature workspace)
    lastVersion := workspace.version
    observationCount := workspace.observations.size
    nodeCount := workspace.atlas.nodes.size
    transitionCount := workspace.atlas.transitions.size
    objectCount := workspace.objects.size
    failureStreak := if recentFailures = 0 then 0 else previous.failureStreak + recentFailures
    confidence := ModelProtocol.clamp01 confidence
    strategy
  }

end ReplanEngine
end ViaLean
