import ViaLean.Proposers.Basic
import ViaLean.Transport

open Lean Meta

namespace ViaLean

/-- Expose kernel-checked equality transports as readable symbolic futures.
The model can select them, reason from them, or ignore them; native search uses
the exact same fact generator independently. -/
def equivTransportProposals
    (goal : GoalSnapshot) (cfg : ProposeConfig) : MetaM (Array Proposal) :=
  goal.goalId.withContext do
    let factLimit := 2 * cfg.maxCandidatesPerFamily * cfg.maxCandidatesPerFamily
    let facts ← equivTransportFacts cfg.maxCandidatesPerFamily factLimit
      cfg.maxProposalSize
    let mut proposals : Array Proposal := #[]
    for fact in facts do
      proposals := proposals.push {
        kind := .cut
        payload := .verifiedCut fact.type fact.proof
        origin := .normalization
        source := fact.source
        prior := 0.88
        estimatedCost := 1.2
        fingerprint := proposalFingerprint .cut fact.type
        explanation? := some
          "Kernel-checked local equality transported through an equivalence"
      }
    return (deduplicateProposals proposals).take cfg.maxCandidatesPerFamily

end ViaLean
