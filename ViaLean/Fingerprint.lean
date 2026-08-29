import ViaLean.Proposal

open Lean

namespace ViaLean

def goalFingerprint (target : Expr) (locals : Array LocalInfo) : UInt64 :=
  locals.foldl (fun acc info => hash (acc, hash info.type)) (hash target)

def proposalFingerprint (kind : ProposalKind) (payload : Expr) : UInt64 :=
  hash (kind, hash payload)

structure SearchPath where
  goalFingerprints     : Std.HashSet UInt64 := {}
  proposalFingerprints : Std.HashSet UInt64 := {}

end ViaLean
