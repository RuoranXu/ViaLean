import ViaLean.Proposers.Basic

open Lean Meta

namespace ViaLean

def witnessProposals (goal : GoalSnapshot) (cfg : ProposeConfig) : MetaM (Array Proposal) := do
  let some (carrier, _) := existsTarget? goal.target | return #[]
  let mut result := #[]
  for info in goal.locals do
    let value := mkFVar info.fvarId
    if ← isDefEq (← inferType value) carrier then
      if let some witness ← validateWitness cfg goal value then
        result := result.push {
          kind := .witness
          payload := .witness witness
          source := "local"
          prior := 0.85
          estimatedCost := 1.0
          fingerprint := proposalFingerprint .witness witness
          explanation? := some s!"local witness {info.userName}"
        }
  return (deduplicateProposals result).take cfg.maxCandidatesPerFamily

end ViaLean
