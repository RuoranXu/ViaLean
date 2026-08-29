import ViaLean.Proposers.Basic

open Lean Meta

namespace ViaLean

def iffProposals (goal : GoalSnapshot) (cfg : ProposeConfig) : MetaM (Array Proposal) := do
  let mut result := #[]
  for info in goal.locals do
    if let some (a, b) := iffTarget? info.type then
      for candidate in #[a, b] do
        if let some mid ← validateIffMid cfg goal candidate then
          result := result.push {
            kind := .iffMid
            payload := .iffMid mid
            source := "local-iff"
            prior := 0.85
            estimatedCost := 2.0
            fingerprint := proposalFingerprint .iffMid mid
          }
  return (deduplicateProposals result).take cfg.maxCandidatesPerFamily

end ViaLean
