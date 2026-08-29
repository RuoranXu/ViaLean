import ViaLean.Search
import ViaLean.Trace

open Lean Parser Tactic Meta Elab Tactic

namespace ViaLean

declare_config_elab proposeConfig ProposeConfig

elab (name := proposeSeq) "propose" config:optConfig : tactic => do
  let cfg ← proposeConfig config
  let goal ← getMainGoal
  match ← runSearch goal cfg with
  | .solved proof _ =>
      goal.assign proof
      replaceMainGoal []
  | .failed _ => throwError "ViaLean found no proof within {cfg.timeoutSec}s"

elab (name := proposeQuery) "propose?" config:optConfig : tactic => do
  let cfg ← proposeConfig config
  logInfo (← diagnose (← getMainGoal) cfg)

syntax (name := proposeViaEqSyntax) "propose" optConfig " via_eq " term : tactic
syntax (name := proposeViaIffSyntax) "propose" optConfig " via_iff " term : tactic
syntax (name := proposeViaCutSyntax) "propose" optConfig " via_cut " term : tactic
syntax (name := proposeViaWitnessSyntax) "propose" optConfig " via_witness " term : tactic

private def closeWithManual
    (goal : MVarId) (cfg : ProposeConfig) (proposal : Proposal) : TacticM Unit := do
  let some proof ← runManualProposal goal cfg proposal
    | throwError "manual ViaLean proposal did not solve the goal"
  checkProof (← goal.getType) proof
  goal.assign proof
  replaceMainGoal []

elab_rules : tactic
  | `(tactic| propose $config:optConfig via_eq $mid:term) => do
      let cfg ← proposeConfig config
      let goal ← getMainGoal
      goal.withContext do
        let snap ← snapshot goal
        let some (carrier, _, _) := eqTarget? snap.target
          | throwError "via_eq requires an equality goal"
        let mid ← Term.elabTerm mid (some carrier)
        let some mid ← validateEqualityMid cfg snap mid
          | throwError "invalid or trivial equality midpoint"
        closeWithManual goal cfg {
          kind := .equalityMid, payload := .equalityMid mid, source := "manual",
          fingerprint := proposalFingerprint .equalityMid mid }
  | `(tactic| propose $config:optConfig via_iff $mid:term) => do
      let cfg ← proposeConfig config
      let goal ← getMainGoal
      goal.withContext do
        let snap ← snapshot goal
        let some _ := iffTarget? snap.target
          | throwError "via_iff requires an equivalence goal"
        let mid ← Term.elabTerm mid none
        let some mid ← validateIffMid cfg snap mid
          | throwError "invalid or trivial equivalence midpoint"
        closeWithManual goal cfg {
          kind := .iffMid, payload := .iffMid mid, source := "manual",
          fingerprint := proposalFingerprint .iffMid mid }
  | `(tactic| propose $config:optConfig via_cut $cut:term) => do
      let cfg ← proposeConfig config
      let goal ← getMainGoal
      goal.withContext do
        let snap ← snapshot goal
        let cut ← Term.elabTerm cut none
        let some cut ← validateCutType cfg snap cut
          | throwError "invalid or no-progress cut type"
        closeWithManual goal cfg {
          kind := .cut, payload := .cutType cut, source := "manual",
          fingerprint := proposalFingerprint .cut cut }
  | `(tactic| propose $config:optConfig via_witness $witness:term) => do
      let cfg ← proposeConfig config
      let goal ← getMainGoal
      goal.withContext do
        let snap ← snapshot goal
        let some (carrier, _) := existsTarget? snap.target
          | throwError "via_witness requires an existential goal"
        let witness ← Term.elabTerm witness (some carrier)
        let some witness ← validateWitness cfg snap witness
          | throwError "invalid witness"
        closeWithManual goal cfg {
          kind := .witness, payload := .witness witness, source := "manual",
          fingerprint := proposalFingerprint .witness witness }

end ViaLean
