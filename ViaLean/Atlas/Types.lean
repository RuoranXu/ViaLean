import ViaLean.Symbolic
import ViaLean.Goal

namespace ViaLean

abbrev AtlasNodeId := UInt64
abbrev TransitionId := UInt64
abbrev RegionId := UInt64

inductive KnowledgeStatus
  | verified | pending | speculative | refuted | dominated
deriving BEq, Hashable, Repr, Inhabited

structure SymbolicSignals where
  exactLocal : Bool := false
  contradiction : Bool := false
  completeInhabitants : Nat := 0
  partialInhabitants : Nat := 0
  subgoals : Nat := 1
deriving BEq, Hashable, Repr, Inhabited

structure AtlasNode where
  id : AtlasNodeId
  key : GoalKey
  snapshot : GoalSnapshot
  depth : Nat
  parent? : Option AtlasNodeId := none
  status : KnowledgeStatus := .verified
  solved : Bool := false
  terminal : Bool := false
  signals : SymbolicSignals := {}
  estimatedCost : Float := 1.0

inductive TransitionOutcome
  | untried | expanded | solved | failed | timedOut | rejected
deriving BEq, Hashable, Repr, Inhabited

structure TransitionEvidence where
  outcome : TransitionOutcome := .untried
  elapsedMs : Nat := 0
  failureClass? : Option String := none
deriving BEq, Hashable, Repr, Inhabited

structure AtlasTransition where
  id : TransitionId
  parent : AtlasNodeId
  candidate : SymbolicTransitionCandidate
  children : Array AtlasNodeId := #[]
  executable : Bool := true
  coupled : Bool := false
  status : KnowledgeStatus := .pending
  evidence : TransitionEvidence := {}
deriving Inhabited

structure RegionSignals where
  solved : Nat := 0
  failed : Nat := 0
  exactLocal : Nat := 0
deriving BEq, Hashable, Repr, Inhabited

structure ProofRegion where
  id : RegionId
  family : StrategyFamily
  entryNodes : Array AtlasNodeId := #[]
  representative : Array AtlasNodeId := #[]
  size : Nat := 0
  minDepth : Nat := 0
  maxDepth : Nat := 0
  signals : RegionSignals := {}
deriving Inhabited

structure AtlasStats where
  transitionsTried : Nat := 0
  nodesCreated : Nat := 0
  metaOps : Nat := 0
  renderedChars : Nat := 0
  transpositions : Nat := 0
  rejectedByBudget : Nat := 0
deriving BEq, Hashable, Repr, Inhabited

structure AtlasLimits where
  maxNodes : Nat
  maxTransitions : Nat
  maxWorkUnits : Nat
  maxMetaOps : Nat
  maxRenderedChars : Nat
  maxRegions : Nat
deriving Inhabited

structure ProofAtlas where
  root? : Option AtlasNodeId := none
  nodes : Array AtlasNode := #[]
  transitions : Array AtlasTransition := #[]
  regions : Array ProofRegion := #[]
  stats : AtlasStats := {}
  nextNode : Nat := 0
  nextTransition : Nat := 0
deriving Inhabited

def AtlasLimits.ofConfig (cfg : ProposeConfig) : AtlasLimits := {
  maxNodes := cfg.atlasMaxNodes
  maxTransitions := cfg.atlasMaxTransitions
  maxWorkUnits := cfg.atlasMaxWorkUnits
  maxMetaOps := cfg.atlasMaxMetaOps
  maxRenderedChars := cfg.atlasMaxRenderedChars
  maxRegions := cfg.atlasMaxRegions
}

def ProofAtlas.node? (atlas : ProofAtlas) (id : AtlasNodeId) : Option AtlasNode :=
  atlas.nodes.find? (·.id == id)

def ProofAtlas.transition? (atlas : ProofAtlas) (id : TransitionId) : Option AtlasTransition :=
  atlas.transitions.find? (·.id == id)

def ProofAtlas.nodeForKey? (atlas : ProofAtlas) (key : GoalKey) : Option AtlasNode :=
  atlas.nodes.find? fun node => node.key.bucket == key.bucket && node.key.strictEq key

def ProofAtlas.observeGoal
    (atlas : ProofAtlas) (limits : AtlasLimits) (snap : GoalSnapshot) (depth : Nat)
    (parent? : Option AtlasNodeId := none) : ProofAtlas × Option AtlasNodeId × Bool :=
  match atlas.nodeForKey? snap.key with
  | some node =>
      ({ atlas with stats := { atlas.stats with
          transpositions := atlas.stats.transpositions + 1 } }, some node.id, false)
  | none =>
      if atlas.nodes.size >= limits.maxNodes then
        ({ atlas with stats := { atlas.stats with
            rejectedByBudget := atlas.stats.rejectedByBudget + 1 } }, none, false)
      else
        let id := UInt64.ofNat atlas.nextNode
        let node : AtlasNode := { id, key := snap.key, snapshot := snap, depth, parent? }
        ({ atlas with
            root? := atlas.root?.orElse (fun _ => some id)
            nodes := atlas.nodes.push node
            nextNode := atlas.nextNode + 1
            stats := { atlas.stats with nodesCreated := atlas.stats.nodesCreated + 1 } },
          some id, true)

def ProofAtlas.offerTransition
    (atlas : ProofAtlas) (limits : AtlasLimits) (parent : AtlasNodeId)
    (candidate : SymbolicTransitionCandidate) : ProofAtlas × Option TransitionId :=
  match atlas.transitions.find? fun t =>
      t.parent == parent && t.candidate.fingerprint == candidate.fingerprint with
  | some transition => (atlas, some transition.id)
  | none =>
      if atlas.transitions.size >= limits.maxTransitions ||
          atlas.stats.transitionsTried >= limits.maxWorkUnits then
        ({ atlas with stats := { atlas.stats with
            rejectedByBudget := atlas.stats.rejectedByBudget + 1 } }, none)
      else
        let id := UInt64.ofNat atlas.nextTransition
        let transition : AtlasTransition := { id, parent, candidate }
        ({ atlas with
            transitions := atlas.transitions.push transition
            nextTransition := atlas.nextTransition + 1
            stats := { atlas.stats with
              transitionsTried := atlas.stats.transitionsTried + 1 } }, some id)

def ProofAtlas.linkChild
    (atlas : ProofAtlas) (transitionId : TransitionId) (child : AtlasNodeId) : ProofAtlas :=
  { atlas with transitions := atlas.transitions.map fun transition =>
      if transition.id == transitionId && !transition.children.contains child then
        { transition with children := transition.children.push child, evidence := {
            transition.evidence with outcome := .expanded } }
      else transition }

def ProofAtlas.recordOutcome
    (atlas : ProofAtlas) (transitionId : TransitionId) (outcome : TransitionOutcome)
    (elapsedMs : Nat) (failureClass? : Option String := none) : ProofAtlas :=
  { atlas with transitions := atlas.transitions.map fun transition =>
      if transition.id == transitionId then
        { transition with
          status := if outcome == .failed || outcome == .rejected then .refuted else .verified
          evidence := { outcome, elapsedMs, failureClass? } }
      else transition }

def ProofAtlas.setNodeSignals
    (atlas : ProofAtlas) (nodeId : AtlasNodeId) (signals : SymbolicSignals) : ProofAtlas :=
  { atlas with nodes := atlas.nodes.map fun node =>
      if node.id == nodeId then { node with signals } else node }

private def pushUnique (values : Array AtlasNodeId) (value : AtlasNodeId) : Array AtlasNodeId :=
  if values.contains value then values else values.push value

/-- Recompute coarse strategy regions from the executable graph. -/
def ProofAtlas.refreshRegions (atlas : ProofAtlas) (maxRegions : Nat) : ProofAtlas := Id.run do
  let mut families : Array StrategyFamily := #[]
  for transition in atlas.transitions do
    unless families.contains transition.candidate.family do
      families := families.push transition.candidate.family
  let mut regions := #[]
  for family in families.take maxRegions do
    let transitions := atlas.transitions.filter (·.candidate.family == family)
    let mut nodeIds := #[]
    let mut solved := 0
    let mut failed := 0
    for transition in transitions do
      nodeIds := pushUnique nodeIds transition.parent
      for child in transition.children do nodeIds := pushUnique nodeIds child
      if transition.evidence.outcome == .solved then solved := solved + 1
      if transition.evidence.outcome == .failed then failed := failed + 1
    let depths := nodeIds.filterMap fun id => (atlas.node? id).map (·.depth)
    let minDepth := depths.foldl (init := depths[0]?.getD 0) min
    let maxDepth := depths.foldl (init := 0) max
    let exactLocal := nodeIds.foldl (init := 0) fun count id =>
      count + if (atlas.node? id).any (·.signals.exactLocal) then 1 else 0
    let depthOf (id : AtlasNodeId) : Nat := (atlas.node? id).map (·.depth) |>.getD 0
    let representative := nodeIds.insertionSort fun left right =>
      depthOf left < depthOf right
    regions := regions.push {
      id := hash family.name
      family
      entryNodes := nodeIds.filter fun id => (atlas.node? id).any (·.depth == minDepth)
      representative := representative.take 3
      size := nodeIds.size
      minDepth
      maxDepth
      signals := { solved, failed, exactLocal }
    }
  return { atlas with regions }

end ViaLean
