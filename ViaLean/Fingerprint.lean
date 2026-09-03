import ViaLean.Proposal

open Lean

namespace ViaLean

def proposalFingerprint (kind : ProposalKind) (payload : Expr) : UInt64 :=
  hash (kind, hash payload)

structure SearchPath where
  goalKeys             : StrictGoalSet := {}
  proposalFingerprints : Std.HashSet UInt64 := {}

end ViaLean
