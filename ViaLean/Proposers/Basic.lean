import ViaLean.Validate

open Lean Meta

namespace ViaLean

structure ProposalProvider where
  name     : String
  generate : GoalSnapshot → ProposeConfig → MetaM (Array Proposal)

def deduplicateProposals (proposals : Array Proposal) : Array Proposal := Id.run do
  let mut seen : Std.HashSet UInt64 := {}
  let mut result := #[]
  for proposal in proposals do
    unless seen.contains proposal.fingerprint do
      seen := seen.insert proposal.fingerprint
      result := result.push proposal
  return result

end ViaLean
