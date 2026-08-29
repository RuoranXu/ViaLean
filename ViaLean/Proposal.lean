import ViaLean.Goal

open Lean

namespace ViaLean

inductive StructuralRule
  | intro | andConstructor | iffConstructor | singleConstructor | existsWithWitness
deriving BEq, Hashable, Repr, Inhabited

inductive ProposalKind
  | direct | cut | equalityMid | iffMid | witness | structural | rewrite | external
deriving BEq, Hashable, Repr, Inhabited

inductive ProposalPayload
  | cutType (type : Expr)
  | equalityMid (mid : Expr)
  | iffMid (mid : Expr)
  | witness (value : Expr)
  | structural (rule : StructuralRule)
deriving Inhabited

structure Proposal where
  kind          : ProposalKind
  payload       : ProposalPayload
  source        : String
  prior         : Float := 0.5
  estimatedCost : Float := 1.0
  fingerprint   : UInt64
  explanation?  : Option String := none

inductive ProposalFamily
  | direct | structural | localCut | libraryCut
  | equalityNormalize | equalityLocal | equalityExternal
  | witnessLocal | witnessExternal | externalCut
deriving BEq, Hashable, Repr, Inhabited

end ViaLean
