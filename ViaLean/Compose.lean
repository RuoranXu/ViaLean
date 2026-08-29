import ViaLean.Action
import ViaLean.Basic

open Lean Meta

namespace ViaLean

def composeAction
    (parentTarget : Expr)
    (plan : CompositionPlan)
    (childProofs : Array Expr) : MetaM Expr := do
  let proof ← match plan with
    | .eqTrans =>
      unless childProofs.size = 2 do throwError "Eq.trans expects two child proofs"
      mkEqTrans childProofs[0]! childProofs[1]!
    | .iffTrans =>
      unless childProofs.size = 2 do throwError "Iff.trans expects two child proofs"
      mkAppM ``Iff.trans #[childProofs[0]!, childProofs[1]!]
    | .iffIntro =>
      unless childProofs.size = 2 do throwError "Iff.intro expects two child proofs"
      mkAppM ``Iff.intro #[childProofs[0]!, childProofs[1]!]
    | .andIntro =>
      unless childProofs.size = 2 do throwError "And.intro expects two child proofs"
      mkAppM ``And.intro #[childProofs[0]!, childProofs[1]!]
    | .existsIntro witness =>
      unless childProofs.size = 1 do throwError "Exists.intro expects one child proof"
      unless parentTarget.isAppOfArity ``Exists 2 do
        throwError "existsIntro requires an existential parent target"
      let args := parentTarget.getAppArgs
      let carrier := args[0]!
      let predicate := args[1]!
      let u ← getLevel carrier
      pure <| mkApp4 (mkConst ``Exists.intro [u])
        carrier predicate witness childProofs[0]!
    | .cutApply _ =>
      unless childProofs.size = 2 do throwError "cutApply expects a proof and continuation"
      pure <| mkApp childProofs[1]! childProofs[0]!
    | .constructor ctor => mkAppM ctor childProofs
    | .sketch count =>
      throwError "structured sketches are not executable in v0.1 (holes: {count})"
  finalizeProof parentTarget proof

end ViaLean
