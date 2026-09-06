import ViaLean.Model.Protocol
import ViaLean.Fingerprint
import ViaLean.Validate
import ViaLean.Workspace

open Lean Meta

namespace ViaLean
namespace ConjectureEngine

def thoughtId (id : String) : UInt64 :=
  id.toNat?.map UInt64.ofNat |>.getD (hash id)

private def resolveReference? (snap : GoalSnapshot) (objects : Array WorkspaceObject)
    (reference : String) : MetaM (Option Expr) := do
  let objectText := if reference.startsWith "object:" then
    String.ofList (reference.toList.drop 7)
  else reference
  if let some id := objectText.toNat? then
    if let some object := objects.find? fun object =>
        object.id == UInt64.ofNat id && object.status != .refuted then
      return some object.expression
  if let some info := snap.locals.find? (toString ·.userName == reference) then
    return some (mkFVar info.fvarId)
  let name := reference.toName
  if (← getEnv).contains name then
    try return some (← mkConstWithFreshMVarLevels name)
    catch _ => return none
  return none

private def originSource (thought : ModelProtocol.PlannerThoughtView) : String :=
  s!"planner:{thought.kind}:{thought.id}"

/-- Compile open-world neural thoughts into independently validated proposal objects.
The v2 DSL references existing locals/constants and never sends raw `Expr` values. -/
def compile (snap : GoalSnapshot) (cfg : ProposeConfig)
    (thoughts : Array ModelProtocol.PlannerThoughtView)
    (objects : Array WorkspaceObject := #[]) : MetaM (Array Proposal × ModelThoughtBatch) :=
  snap.goalId.withContext do
    let mut proposals : Array Proposal := #[]
    let mut acceptedThoughts : Array ModelThought := #[]
    for thought in thoughts do
      let dependencyIds := thought.dependencies.map thoughtId
      let dependenciesReady := dependencyIds.all fun id =>
        acceptedThoughts.any (·.id == id) ||
        objects.any fun object => object.id == id && object.status != .refuted
      unless dependenciesReady do continue
      let saved ← saveState
      let some term ← resolveReference? snap objects thought.expressionRef
        | saved.restore; continue
      let kind := thought.kind.trimAscii.toString.toLower
      let proposal? : Option Proposal ← try
        if kind == "direct_term" || kind == "exact" then
          let type ← inferType term
          if ← isDefEq type snap.target then
            pure <| some {
              kind := .direct
              payload := .directTerm term
              origin := .planner
              source := originSource thought
              prior := 0.85
              estimatedCost := 0.5
              fingerprint := proposalFingerprint .direct term }
          else pure none
        else if kind == "equality_bridge" then
          pure <| (← validateEqualityMid cfg snap term).map fun mid => {
            kind := .equalityMid
            payload := .equalityMid mid
            origin := .planner
            source := originSource thought
            prior := 0.8
            estimatedCost := 2.0
            fingerprint := proposalFingerprint .equalityMid mid }
        else if kind == "iff_bridge" then
          pure <| (← validateIffMid cfg snap term).map fun mid => {
            kind := .iffMid
            payload := .iffMid mid
            origin := .planner
            source := originSource thought
            prior := 0.8
            estimatedCost := 2.0
            fingerprint := proposalFingerprint .iffMid mid }
        else if kind == "witness" || kind == "intermediate_value" then
          pure <| (← validateWitness cfg snap term).map fun witness => {
            kind := .witness
            payload := .witness witness
            origin := .planner
            source := originSource thought
            prior := 0.85
            estimatedCost := 1.0
            fingerprint := proposalFingerprint .witness witness }
        else if kind == "helper_lemma" || kind == "cut" then
          let proposition ← inferType term
          pure <| (← validateCutType cfg snap proposition).map fun cut => {
            kind := .cut
            payload := .cutType cut
            origin := .planner
            source := originSource thought
            prior := 0.75
            estimatedCost := 2.5
            fingerprint := proposalFingerprint .cut cut }
        else pure none
      catch _ => pure none
      if let some proposal := proposal? then
        proposals := proposals.push proposal
        let conjectureKind : ConjectureKind := match kind with
          | "direct_term" | "exact" => .term
          | "equality_bridge" => .equalityBridge
          | "iff_bridge" => .iffBridge
          | "witness" | "intermediate_value" => .witness
          | _ => .helperLemma
        acceptedThoughts := acceptedThoughts.push {
          id := thoughtId thought.id
          kind := conjectureKind
          expression := term
          dependencies := thought.dependencies.map thoughtId
        }
      else
        saved.restore
    let batch : ModelThoughtBatch := { epoch := 0, thoughts := acceptedThoughts }
    return (proposals, batch)

end ConjectureEngine
end ViaLean
