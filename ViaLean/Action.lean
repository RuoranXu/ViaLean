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
  | { kind := .equalityMid, source, .. } =>
      if source.startsWith "external" then .equalityExternal
      else if source.startsWith "local" then .equalityLocal
      else .equalityNormalize
  | { kind := .witness, source, .. } =>
      if source.startsWith "external" then .witnessExternal else .witnessLocal
  | { kind := .cut, source, .. } =>
      if source.startsWith "external" then .externalCut
      else if source.startsWith "library" then .libraryCut
      else .localCut
  | { kind := .structural, .. } => .structural
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
