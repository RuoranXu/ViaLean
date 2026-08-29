import ViaLean.Proposers.Basic

open Lean Meta

namespace ViaLean

def equalityProposals (goal : GoalSnapshot) (cfg : ProposeConfig) : MetaM (Array Proposal) := do
  let some (carrier, _, _) := eqTarget? goal.target | return #[]
  let mut result := #[]
  for info in goal.locals do
    let value := mkFVar info.fvarId
    if ← isDefEq (← inferType value) carrier then
      if let some mid ← validateEqualityMid cfg goal value then
        result := result.push {
          kind := .equalityMid
          payload := .equalityMid mid
          source := "local"
          prior := 0.8
          estimatedCost := 2.0
          fingerprint := proposalFingerprint .equalityMid mid
          explanation? := some s!"local term {info.userName}"
        }
    if let some (_, a, b) := eqTarget? info.type then
      for mid in #[a, b] do
        if let some mid ← validateEqualityMid cfg goal mid then
          result := result.push {
            kind := .equalityMid
            payload := .equalityMid mid
            source := "local-equality"
            prior := 0.9
            estimatedCost := 2.0
            fingerprint := proposalFingerprint .equalityMid mid
          }
  return (deduplicateProposals result).take cfg.maxCandidatesPerFamily

end ViaLean
