import ViaLean.Proposers.Basic

open Lean Meta

namespace ViaLean

private def addCut?
    (cfg : ProposeConfig) (goal : GoalSnapshot) (candidate : Expr)
    (result : Array Proposal) : MetaM (Array Proposal) := do
  let some cut ← validateCutType cfg goal candidate | return result
  return result.push {
    kind := .cut
    payload := .cutType cut
    source := "local"
    prior := 0.7
    estimatedCost := 2.0
    fingerprint := proposalFingerprint .cut cut
  }

def localCutProposals (goal : GoalSnapshot) (cfg : ProposeConfig) : MetaM (Array Proposal) := do
  let mut result := #[]
  for info in goal.locals do
    let type ← whnf info.type
    if let .forallE _ domain body _ := type then
      if !body.hasLooseBVar 0 then
        result ← addCut? cfg goal body result
      if !domain.hasLooseBVar 0 then
        result ← addCut? cfg goal domain result
    if let some (_, a, b) := eqTarget? type then
      if ← isProp a then result ← addCut? cfg goal a result
      if ← isProp b then result ← addCut? cfg goal b result
  return (deduplicateProposals result).take cfg.maxCandidatesPerFamily

end ViaLean
