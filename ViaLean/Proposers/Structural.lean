import ViaLean.Proposers.Basic

namespace ViaLean

def structuralProposals (goal : GoalSnapshot) (_cfg : ProposeConfig) : Array Proposal :=
  let rule? := match goal.shape with
    | .forall => some StructuralRule.intro
    | .conjunction => some .andConstructor
    | .iff => some .iffConstructor
    | _ => none
  match rule? with
  | none => #[]
  | some rule => #[{
      kind := .structural
      payload := .structural rule
      source := "structural"
      prior := 1.0
      estimatedCost := 1.0
      fingerprint := hash (ProposalKind.structural, rule)
    }]

end ViaLean
