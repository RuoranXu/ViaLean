import ViaLean.Proposal

open Lean

namespace ViaLean

def proposalFingerprint (kind : ProposalKind) (payload : Expr) : UInt64 :=
  hash (kind, hash payload)
structure ProposalKey where
  kind : ProposalKind
  payload : ProposalPayload
  bucket : UInt64

def ProposalKey.ofProposal (proposal : Proposal) : ProposalKey := {
  kind := proposal.kind
  payload := proposal.payload
  bucket := proposal.fingerprint
}

private def ProposalPayload.strictEq : ProposalPayload → ProposalPayload → Bool
  | .directTerm left, .directTerm right => left == right
  | .cutType left, .cutType right => left == right
  | .libraryApply left, .libraryApply right => left == right
  | .equalityMid left, .equalityMid right => left == right
  | .iffMid left, .iffMid right => left == right
  | .witness left, .witness right => left == right
  | .structural left, .structural right => left == right
  | _, _ => false

def ProposalKey.strictEq (left right : ProposalKey) : Bool :=
  left.kind == right.kind && left.payload.strictEq right.payload

structure StrictProposalSet where
  buckets : Std.HashMap UInt64 (Array ProposalKey) := {}
deriving Inhabited

def StrictProposalSet.contains (set : StrictProposalSet) (key : ProposalKey) : Bool :=
  (set.buckets.get? key.bucket).any fun keys => keys.any (·.strictEq key)

def StrictProposalSet.insert (set : StrictProposalSet) (key : ProposalKey) : StrictProposalSet :=
  if set.contains key then set else
    let keys := (set.buckets.get? key.bucket).getD #[]
    { buckets := set.buckets.insert key.bucket (keys.push key) }


structure SearchPath where
  goalKeys             : StrictGoalSet := {}
  proposals            : StrictProposalSet := {}

end ViaLean
