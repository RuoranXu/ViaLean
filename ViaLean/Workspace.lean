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
  type? : Option Expr := none
  blockers : Array UInt64 := #[]
  utility : Float := 0.5
  dependencies : Array UInt64 := #[]
  status : KnowledgeStatus := .speculative
  origin : TransitionOrigin := .model

inductive FailureClass
  | typeMismatch | unification | noProgress | branchGrowth | branchExplosion
  | timeout | unsafeSyntax | rewriteNoMatch | premiseMismatch | openGoals
  | invalidPlannerSelection | budgetDenied | internal | unknown
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

/-- Reserve one unit from the single Atlas Meta-operation budget. -/
def reserveMetaOp (ref : IO.Ref ProofWorkspace) (cfg : ProposeConfig)
    (count : Nat := 1) : IO Bool := do
  let workspace ← ref.get
  if workspace.atlas.stats.metaOps + count > cfg.atlasMaxMetaOps then
    ref.set { workspace with atlas := { workspace.atlas with stats := {
      workspace.atlas.stats with
      rejectedByBudget := workspace.atlas.stats.rejectedByBudget + 1 } } }
    return false
  ref.set { workspace with atlas := workspace.atlas.recordMetaOp count }
  return true

def observePreviewGoal (ref : IO.Ref ProofWorkspace) (cfg : ProposeConfig)
    (snap : GoalSnapshot) (depth : Nat) (renderedGoal : String)
    (parent? : Option AtlasNodeId := none) : IO (Option AtlasNodeId × Bool) := do
  let workspace ← ref.get
  let (atlas, nodeId?, created) :=
    workspace.atlas.observePreview (.ofConfig cfg) snap depth renderedGoal parent?
  ref.set { workspace with atlas, version := workspace.version + (if created then 1 else 0) }
  return (nodeId?, created)

def offerPreviewTransition (ref : IO.Ref ProofWorkspace) (cfg : ProposeConfig)
    (parent : AtlasNodeId) (candidate : SymbolicTransitionCandidate) :
    IO (Option TransitionId) := do
  let workspace ← ref.get
  let (atlas, transition?) :=
    workspace.atlas.offerTransition (.ofConfig cfg) parent candidate false
  let changed := atlas.transitions.size != workspace.atlas.transitions.size
  ref.set { workspace with atlas, version := workspace.version + (if changed then 1 else 0) }
  return transition?

def linkPreviewChild (ref : IO.Ref ProofWorkspace)
    (transition : TransitionId) (child : AtlasNodeId) : IO Unit :=
  ref.modify fun workspace => { workspace with
    atlas := workspace.atlas.linkChild transition child
    version := workspace.version + 1 }

def finishPreviewTransition (ref : IO.Ref ProofWorkspace)
    (transition : TransitionId) (outcome : TransitionOutcome) : IO Unit :=
  ref.modify fun workspace => { workspace with
    atlas := workspace.atlas.recordOutcome transition outcome 0
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
    let childNodes := (workspace.atlas.transition? transition).map
      (·.children) |>.getD #[]
    let observation : StructuredObservation := {
      sequence := workspace.observations.size
      transition? := some transition
      outcome
      failureClass?
      elapsedMs
      newNodes := childNodes
    }
    { workspace with
      atlas := workspace.atlas.recordOutcome transition outcome elapsedMs
        (failureClass?.map fun failure => (repr failure).pretty)
      observations := workspace.observations.push observation
      version := workspace.version + 1 }

def recordObservation (ref : IO.Ref ProofWorkspace)
    (outcome : TransitionOutcome) (failureClass? : Option FailureClass := none)
    (transition? : Option TransitionId := none) (newNodes : Array AtlasNodeId := #[])
    (elapsedMs : Nat := 0) (debug? : Option String := none) : IO Unit :=
  ref.modify fun workspace =>
    let observation : StructuredObservation := {
      sequence := workspace.observations.size
      transition?
      outcome
      failureClass?
      newNodes
      elapsedMs
      debug?
    }
    { workspace with
      observations := workspace.observations.push observation
      version := workspace.version + 1 }

/-- Absorb each thought independently. This records hypotheses; it never marks them verified. -/
private def statusRank : KnowledgeStatus → Nat
  | .refuted => 0
  | .dominated => 1
  | .speculative => 2
  | .pending => 3
  | .verified => 4

def registerObject (ref : IO.Ref ProofWorkspace) (kind : ConjectureKind)
    (expression : Expr) (type? : Option Expr := none)
    (status : KnowledgeStatus := .verified) (origin : TransitionOrigin := .derived)
    (dependencies : Array UInt64 := #[]) (blockers : Array UInt64 := #[])
    (utility : Float := 0.5) : IO (UInt64 × Bool) := do
  let workspace ← ref.get
  if let some existing := workspace.objects.find? fun object =>
      object.kind == kind && object.expression == expression &&
        object.type? == type? then
    if statusRank status > statusRank existing.status then
      let objects := workspace.objects.map fun object =>
        if object.id == existing.id then { object with status } else object
      ref.set { workspace with objects, version := workspace.version + 1 }
    return (existing.id, false)
  let baseId : UInt64 := hash (kind, hash expression, type?.map hash)
  let id := if workspace.objects.any (·.id == baseId) then
    hash (baseId, workspace.objects.size)
  else baseId
  let object : WorkspaceObject := {
    id, kind, expression, type?, dependencies, blockers, status, origin, utility }
  ref.set { workspace with
    objects := workspace.objects.push object
    version := workspace.version + 1 }
  return (id, true)

def setObjectStatus (ref : IO.Ref ProofWorkspace) (id : UInt64)
    (status : KnowledgeStatus) : IO Bool := do
  let workspace ← ref.get
  let some existing := workspace.objects.find? (·.id == id) | return false
  if existing.status == status then return false
  ref.set { workspace with
    objects := workspace.objects.map fun object =>
      if object.id == id then { object with status } else object
    version := workspace.version + 1 }
  return true

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
