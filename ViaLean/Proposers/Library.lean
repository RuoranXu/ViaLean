import ViaLean.Proposers.Basic
import ViaLean.Premise.Library

open Lean Meta

namespace ViaLean

private def candidateCodomain (name : Name) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels name
  let mut type ← inferType constant
  let mut keepPeeling := true
  while keepPeeling do
    match ← whnf type with
    | .forallE _ _ body _ =>
        if body.hasLooseBVar 0 then keepPeeling := false
        else type := body
    | _ => keepPeeling := false
  instantiateMVars type

def libraryCutProposals
    (goal : GoalSnapshot) (cfg : ProposeConfig)
    (premises : Array PremiseCandidate) : MetaM (Array Proposal) := do
  let mut result := #[]
  for premise in premises do
    try
      let candidate ← candidateCodomain premise.name
      if let some cut ← validateCutType cfg goal candidate then
        result := result.push {
          kind := .cut
          payload := .cutType cut
          source := s!"library:{premise.name}"
          prior := min 1.0 (0.4 + premise.score * 0.4)
          estimatedCost := 2.5
          fingerprint := proposalFingerprint .cut cut
        }
    catch _ => pure ()
  return (deduplicateProposals result).take cfg.maxCandidatesPerFamily

end ViaLean
