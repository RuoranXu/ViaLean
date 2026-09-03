import ViaLean.Proposal
import ViaLean.Solver.Basic

open Lean

namespace ViaLean

inductive ProofActionPayload
  | close (solver : SolverKind)
  | structural (rule : StructuralRule)
  | proposal (proposal : Proposal)
  | sketch (holeTypes : Array Expr)
deriving Inhabited

inductive CompositionPlan
  | eqTrans | iffTrans | iffIntro | andIntro
  | existsIntro (witness : Expr)
  | cutApply (cutType : Expr)
  | constructor (ctor : Name)
  | sketch (holeCount : Nat)
deriving Inhabited

structure ProofAction where
  payload     : ProofActionPayload
  family      : ProposalFamily
  prior       : Float := 0.5
  estimatedCost : Float := 1.0
  fingerprint : UInt64

structure GoalBundle where
  goals       : Array MVarId
  coupled     : Bool := false
  sharedMVars : Array MVarId := #[]
  composition : CompositionPlan

inductive ActionExpansion
  | closed (proof : Expr)
  | open (bundle : GoalBundle)

def Proposal.family : Proposal → ProposalFamily
  | { kind := .equalityMid, origin, .. } =>
      match origin with
      | .external | .planner => .equalityExternal
      | .local => .equalityLocal
      | _ => .equalityNormalize
  | { kind := .witness, origin, .. } =>
      match origin with
      | .external | .planner => .witnessExternal
      | _ => .witnessLocal
  | { kind := .cut, origin, .. } =>
      match origin with
      | .external | .planner => .externalCut
      | .library _ => .libraryCut
      | _ => .localCut
  | { kind := .structural, .. } => .structural
  | { kind := .direct, .. } => .direct
  | _ => .direct

def Proposal.compile (proposal : Proposal) : ProofAction := {
  payload := .proposal proposal
  family := proposal.family
  prior := proposal.prior
  estimatedCost := proposal.estimatedCost
  fingerprint := proposal.fingerprint
}

def structuralAction (rule : StructuralRule) : ProofAction := {
  payload := .structural rule
  family := .structural
  prior := 1.0
  fingerprint := hash (ProposalKind.structural, rule)
}

def nativeCloseAction : ProofAction := {
  payload := .close .native
  family := .direct
  prior := 1.0
  fingerprint := hash ("close", "native")
}

end ViaLean
