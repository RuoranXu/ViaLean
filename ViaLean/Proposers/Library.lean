import ViaLean.Proposers.Basic
import ViaLean.Premise.Library

open Lean Meta

namespace ViaLean

def libraryCutProposals
    (_goal : GoalSnapshot) (cfg : ProposeConfig)
    (premises : Array PremiseCandidate) : MetaM (Array Proposal) := do
  let mut result := #[]
  for premise in premises do
    try
      let theoremType ← instantiateMVars (← inferType (← mkConstWithFreshMVarLevels premise.name))
      if exprSize theoremType ≤ cfg.maxProposalSize then
        result := result.push {
          kind := .cut
          payload := .libraryApply premise.name
          source := s!"library:{premise.name}"
          prior := min 1.0 (0.4 + premise.score * 0.4)
          estimatedCost := 2.5
          fingerprint := hash (ProposalKind.cut, premise.name)
        }
    catch _ => pure ()
  return (deduplicateProposals result).take cfg.maxCandidatesPerFamily

end ViaLean
