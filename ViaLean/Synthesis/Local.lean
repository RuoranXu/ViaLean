import ViaLean.Workspace
import ViaLean.Validate

open Lean Meta

namespace ViaLean

structure SynthesisCandidate where
  term : Expr
  obligations : Array Expr := #[]
  operation : SymbolicOperation
  cost : Nat := 1
deriving Inhabited

def SynthesisCandidate.complete (candidate : SynthesisCandidate) : Bool :=
  candidate.obligations.isEmpty

namespace LocalSynthesizer

private partial def arrowDomains (type : Expr) (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[]
  match ← whnf type with
  | .forallE _ domain body _ =>
      if body.hasLooseBVar 0 then return #[domain]
      return #[domain] ++ (← arrowDomains body (fuel - 1))
  | _ => return #[]

/-- Produce multiple complete inhabitants and partial local applications at every visited goal. -/
def synthesize (snap : GoalSnapshot) (maxCandidates : Nat) : MetaM (Array SynthesisCandidate) :=
  snap.goalId.withContext do
    let mut result := #[]
    for info in snap.locals do
      if result.size >= maxCandidates then break
      if ← isDefEq info.type snap.target then
        result := result.push {
          term := mkFVar info.fvarId, operation := .exactLocal info.fvarId, cost := 0 }
      else
        let gaps ← arrowDomains info.type 4
        unless gaps.isEmpty do
          result := result.push {
            term := mkFVar info.fvarId, obligations := gaps
            operation := .applyLocal info.fvarId, cost := gaps.size }
    if result.size < maxCandidates then
      if let some (_, lhs, rhs) := eqTarget? snap.target then
        if ← isDefEq lhs rhs then
          result := result.push {
            term := ← mkAppM ``Eq.refl #[lhs]
            operation := .simplifyTarget
            cost := 0
          }
    if result.size < maxCandidates && snap.target.isConstOf ``True then
      result := result.push {
        term := mkConst ``True.intro
        operation := .constructor ``True.intro
        cost := 0
      }
    return result

def firstComplete? (candidates : Array SynthesisCandidate) : Option Expr :=
  (candidates.find? (·.complete)).map (·.term)

end LocalSynthesizer
end ViaLean
