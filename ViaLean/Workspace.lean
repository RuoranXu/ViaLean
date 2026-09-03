import ViaLean.Atlas.Types

open Lean

namespace ViaLean

inductive ConjectureKind
  | helperLemma | equalityBridge | iffBridge | witness | invariant | generalization | term
deriving BEq, Hashable, Repr, Inhabited

structure WorkspaceObject where
  id : UInt64
  kind : ConjectureKind
  expression : Expr
  dependencies : Array UInt64 := #[]
  status : KnowledgeStatus := .speculative
  origin : TransitionOrigin := .model

inductive FailureClass
  | typeMismatch | unification | noProgress | branchGrowth | timeout | unsafeSyntax | unknown
deriving BEq, Hashable, Repr, Inhabited

structure StructuredObservation where
  sequence : Nat
  transition? : Option TransitionId := none
  outcome : TransitionOutcome
  failureClass? : Option FailureClass := none
  newNodes : Array AtlasNodeId := #[]
  elapsedMs : Nat := 0
  debug? : Option String := none
deriving Inhabited

structure ModelThought where
  id : UInt64
  kind : ConjectureKind
  expression : Expr
  dependencies : Array UInt64 := #[]

structure ModelThoughtBatch where
  epoch : Nat
  thoughts : Array ModelThought := #[]
deriving Inhabited

structure WorkspaceDelta where
  fromVersion : Nat
  toVersion : Nat
  addedNodes : Array AtlasNodeId := #[]
  addedTransitions : Array TransitionId := #[]
  verifiedObjects : Array UInt64 := #[]
  refutedObjects : Array UInt64 := #[]
  observations : Array StructuredObservation := #[]
deriving Inhabited

structure ProofWorkspace where
  version : Nat := 0
  atlas : ProofAtlas := {}
  objects : Array WorkspaceObject := #[]
  observations : Array StructuredObservation := #[]
  neuralEpoch : Nat := 0
deriving Inhabited

namespace Workspace

def observeGoal (ref : IO.Ref ProofWorkspace) (cfg : ProposeConfig)
    (snap : GoalSnapshot) (depth : Nat) (parentTransition? : Option TransitionId := none) :
    IO (Option AtlasNodeId) := do
  let workspace ← ref.get
  let parentNode? := parentTransition?.bind fun transition =>
    (workspace.atlas.transition? transition).map (·.parent)
  let (atlas, nodeId?, created) := workspace.atlas.observeGoal (.ofConfig cfg) snap depth parentNode?
  let atlas := match parentTransition?, nodeId? with
    | some transition, some node => atlas.linkChild transition node
    | _, _ => atlas
  ref.set { workspace with atlas, version := workspace.version + (if created then 1 else 0) }
  return nodeId?

def setSynthesisSignals (ref : IO.Ref ProofWorkspace) (nodeId : AtlasNodeId)
    (signals : SymbolicSignals) : IO Unit :=
  ref.modify fun workspace => { workspace with
    atlas := workspace.atlas.setNodeSignals nodeId signals
    version := workspace.version + 1 }

def offerActions (ref : IO.Ref ProofWorkspace) (cfg : ProposeConfig)
    (parent : AtlasNodeId) (actions : Array ProofAction) : IO Unit :=
  ref.modify fun workspace =>
    let atlas := actions.foldl (init := workspace.atlas) fun atlas action =>
      (atlas.offerTransition (.ofConfig cfg) parent action.toSymbolic).1
    let changed := atlas.transitions.size != workspace.atlas.transitions.size
    { workspace with atlas, version := workspace.version + (if changed then 1 else 0) }

def refreshRegions (ref : IO.Ref ProofWorkspace) (maxRegions : Nat) : IO ProofWorkspace := do
  ref.modify fun workspace => { workspace with
    atlas := workspace.atlas.refreshRegions maxRegions }
  ref.get

def beginAction (ref : IO.Ref ProofWorkspace) (cfg : ProposeConfig)
    (snap : GoalSnapshot) (action : ProofAction) : IO (Option TransitionId) := do
  let workspace ← ref.get
  let some parent := workspace.atlas.nodeForKey? snap.key | return none
  let (atlas, transition?) := workspace.atlas.offerTransition (.ofConfig cfg) parent.id action.toSymbolic
  ref.set { workspace with atlas, version := workspace.version + 1 }
  return transition?

def finishAction (ref : IO.Ref ProofWorkspace) (transition? : Option TransitionId)
    (outcome : TransitionOutcome) (elapsedMs : Nat)
    (failureClass? : Option FailureClass := none) : IO Unit := do
  let some transition := transition? | return
  ref.modify fun workspace =>
    let observation : StructuredObservation := {
      sequence := workspace.observations.size
      transition? := some transition
      outcome
      failureClass?
      elapsedMs
    }
    { workspace with
      atlas := workspace.atlas.recordOutcome transition outcome elapsedMs
        (failureClass?.map fun failure => (repr failure).pretty)
      observations := workspace.observations.push observation
      version := workspace.version + 1 }

/-- Absorb each thought independently. This records hypotheses; it never marks them verified. -/
def absorbThoughtBatch (ref : IO.Ref ProofWorkspace) (batch : ModelThoughtBatch) : IO WorkspaceDelta := do
  let before ← ref.get
  let mut objects := before.objects
  for thought in batch.thoughts do
    unless objects.any (·.id == thought.id) do
      objects := objects.push {
        id := thought.id
        kind := thought.kind
        expression := thought.expression
        dependencies := thought.dependencies
        status := .speculative
        origin := .model
      }
  let added := objects.size - before.objects.size
  let after := { before with
    objects
    neuralEpoch := max before.neuralEpoch batch.epoch
    version := before.version + added }
  ref.set after
  return { fromVersion := before.version, toVersion := after.version }

end Workspace
end ViaLean
