import ViaLean.Model.Protocol
import ViaLean.Model.Syntax
import ViaLean.Fingerprint
import ViaLean.Proposers.Basic
import ViaLean.Validate
import ViaLean.Workspace
import Lean.Elab.Term

open Lean Meta

namespace ViaLean
namespace ConjectureEngine

def thoughtId (id : String) : UInt64 :=
  id.toNat?.map UInt64.ofNat |>.getD (hash id)

structure ThoughtRejection where
  id : UInt64
  failureClass : FailureClass
  detail : String
deriving Inhabited

structure CompileResult where
  proposals : Array Proposal := #[]
  batch : ModelThoughtBatch := { epoch := 0 }
  rejections : Array ThoughtRejection := #[]
deriving Inhabited

private structure ResolvedThought where
  term : Expr
  fromSurface : Bool := false
  display : String

private def bounded (limit : Nat) (text : String) : String :=
  if text.length <= limit then text else (text.take limit).toString ++ "…"

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

private def surfaceExpectedType? (snap : GoalSnapshot) (kind : String) : Option Expr :=
  if kind == "direct_term" || kind == "exact" then some snap.target
  else if kind == "equality_bridge" then (eqTarget? snap.target).map (·.1)
  else if kind == "iff_bridge" then (iffTarget? snap.target).map fun _ => mkSort .zero
  else if kind == "witness" || kind == "intermediate_value" then
    (existsTarget? snap.target).map (·.1)
  else if kind == "helper_lemma" || kind == "cut" || kind == "invariant" ||
      kind == "generalization" then some (mkSort .zero)
  else none

private def elaborateSurface
    (cfg : ProposeConfig) (source : String) (expectedType : Expr) :
    MetaM (Except (FailureClass × String) Expr) := do
  if source.trimAscii.isEmpty then
    return .error (.unsafeSyntax, "empty structured expression")
  if source.length > cfg.modelMaxCodeChars then
    return .error (.unsafeSyntax,
      s!"structured expression exceeds {cfg.modelMaxCodeChars} characters")
  let termSyntax ← match parseSafeModelTerm (← getEnv) source with
    | .ok termSyntax => pure termSyntax
    | .error error => return .error (.unsafeSyntax, bounded 512 error)
  let originalEnv ← getEnv
  try
    let term ←
      withOptions (fun options =>
          options.setNat `maxHeartbeats cfg.modelCodeMaxHeartbeats) do
        withCurrHeartbeats do
          Elab.Term.TermElabM.run' <|
            Elab.Term.withoutErrToSorry <| Elab.Term.withSynthesize <|
              Elab.Term.elabTerm termSyntax (some expectedType)
    modifyEnv fun _ => originalEnv
    let term ← instantiateMVars term
    if term.hasMVar || term.hasLooseBVars || containsSorry term ||
        exprSize term > cfg.maxProposalSize then
      return .error (.typeMismatch,
        "structured expression left metavariables, loose binders, sorry, or exceeded the size bound")
    return .ok term
  catch error =>
    modifyEnv fun _ => originalEnv
    let detail ← try error.toMessageData.toString catch _ =>
      pure "structured expression elaboration failed"
    return .error (.typeMismatch, bounded 512 detail)

private def resolveThought
    (snap : GoalSnapshot) (cfg : ProposeConfig) (objects : Array WorkspaceObject)
    (thought : ModelProtocol.PlannerThoughtView) (kind : String) :
    MetaM (Except (FailureClass × String) ResolvedThought) := do
  if let some source := thought.expression? then
    let some expectedType := surfaceExpectedType? snap kind
      | return .error (.noProgress, s!"thought kind {kind} is unsupported at this goal shape")
    match ← elaborateSurface cfg source expectedType with
    | .ok term => return .ok { term, fromSurface := true, display := bounded 1024 source }
    | .error error => return .error error
  if thought.expressionRef.isEmpty then
    return .error (.invalidPlannerSelection, "thought has neither expression nor expression_ref")
  let some term ← resolveReference? snap objects thought.expressionRef
    | return .error (.premiseMismatch,
        s!"unknown or refuted expression_ref {bounded 160 thought.expressionRef}")
  return .ok { term, display := bounded 1024 thought.expressionRef }

private def helperCandidate (resolved : ResolvedThought) : MetaM (Option Expr) := do
  if resolved.fromSurface || (← isProp resolved.term) then return some resolved.term
  let type ← instantiateMVars (← inferType resolved.term)
  if ← isProp type then return some type else return none

/-- Compile open-world neural thoughts into independently validated proposals.
Each structured expression is parsed as a term (never a tactic), elaborated under
strict bounds, and checked against the semantic role implied by `kind`. -/
def compile (snap : GoalSnapshot) (cfg : ProposeConfig)
    (thoughts : Array ModelProtocol.PlannerThoughtView)
    (objects : Array WorkspaceObject := #[]) : MetaM CompileResult :=
  snap.goalId.withContext do
    let mut proposals : Array Proposal := #[]
    let mut acceptedThoughts : Array ModelThought := #[]
    let mut rejections : Array ThoughtRejection := #[]
    for thought in thoughts do
      let id := thoughtId thought.id
      let dependencyIds := thought.dependencies.map thoughtId
      let dependenciesReady := dependencyIds.all fun dependency =>
        acceptedThoughts.any (·.id == dependency) ||
        objects.any fun object => object.id == dependency && object.status != .refuted
      unless dependenciesReady do
        rejections := rejections.push {
          id, failureClass := .premiseMismatch
          detail := s!"thought:{thought.id}: unresolved dependency" }
        continue
      let saved ← saveState
      let kind := thought.kind.trimAscii.toString.toLower
      let resolved ← match ← resolveThought snap cfg objects thought kind with
        | .ok resolved => pure resolved
        | .error (failureClass, detail) =>
            saved.restore
            rejections := rejections.push {
              id, failureClass, detail := s!"thought:{thought.id}: {detail}" }
            continue
      let compiled : Option (Proposal × ConjectureKind × Expr) ← try
        if kind == "direct_term" || kind == "exact" then
          let type ← inferType resolved.term
          if ← isDefEq type snap.target then
            pure <| some ({
              kind := .direct
              payload := .directTerm resolved.term
              origin := .planner
              source := originSource thought
              prior := 0.85
              estimatedCost := 0.5
              fingerprint := proposalFingerprint .direct resolved.term },
              .term, resolved.term)
          else pure none
        else if kind == "equality_bridge" then
          pure <| (← validateEqualityMid cfg snap resolved.term).map fun mid => ({
            kind := .equalityMid
            payload := .equalityMid mid
            origin := .planner
            source := originSource thought
            prior := 0.8
            estimatedCost := 2.0
            fingerprint := proposalFingerprint .equalityMid mid },
            .equalityBridge, mid)
        else if kind == "iff_bridge" then
          pure <| (← validateIffMid cfg snap resolved.term).map fun mid => ({
            kind := .iffMid
            payload := .iffMid mid
            origin := .planner
            source := originSource thought
            prior := 0.8
            estimatedCost := 2.0
            fingerprint := proposalFingerprint .iffMid mid },
            .iffBridge, mid)
        else if kind == "witness" || kind == "intermediate_value" then
          pure <| (← validateWitness cfg snap resolved.term).map fun witness => ({
            kind := .witness
            payload := .witness witness
            origin := .planner
            source := originSource thought
            prior := 0.85
            estimatedCost := 1.0
            fingerprint := proposalFingerprint .witness witness },
            .witness, witness)
        else if kind == "helper_lemma" || kind == "cut" || kind == "invariant" ||
            kind == "generalization" then
          let some candidate ← helperCandidate resolved | pure none
          pure <| (← validateCutType cfg snap candidate).map fun cut => ({
            kind := .cut
            payload := .cutType cut
            origin := .planner
            source := originSource thought
            prior := 0.75
            estimatedCost := 2.5
            fingerprint := proposalFingerprint .cut cut },
            if kind == "invariant" then .invariant
            else if kind == "generalization" then .generalization
            else .helperLemma, cut)
        else pure none
      catch _ => pure none
      match compiled with
      | some (proposal, conjectureKind, expression) =>
          let display ← try pure (bounded 1024 (← ppExpr expression).pretty)
            catch _ => pure resolved.display
          proposals := proposals.push proposal
          acceptedThoughts := acceptedThoughts.push {
            id
            kind := conjectureKind
            expression
            dependencies := dependencyIds
            display? := some display
          }
      | none =>
          saved.restore
          rejections := rejections.push {
            id, failureClass := .noProgress
            detail := s!"thought:{thought.id}: expression did not match its kind or goal shape" }
    return {
      proposals := deduplicateProposals proposals
      batch := { epoch := 0, thoughts := acceptedThoughts }
      rejections
    }

end ConjectureEngine
end ViaLean
