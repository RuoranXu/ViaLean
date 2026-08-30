import ViaLean.Model.Provider
import ViaLean.Trace

open Lean Meta

namespace ViaLean

namespace ModelGuidanceEngine

private def familyName : ProposalFamily → String
  | .direct => "direct"
  | .structural => "structural"
  | .localCut => "local_cut"
  | .libraryCut => "library_cut"
  | .equalityNormalize => "equality_normalize"
  | .equalityLocal => "equality_local"
  | .equalityExternal => "equality_external"
  | .witnessLocal => "witness_local"
  | .witnessExternal => "witness_external"
  | .externalCut => "external_cut"

private def kindName : ProposalKind → String
  | .direct => "direct"
  | .cut => "cut"
  | .equalityMid => "equality_mid"
  | .iffMid => "iff_mid"
  | .witness => "witness"
  | .structural => "structural"
  | .rewrite => "rewrite"
  | .external => "external"

private def shapeName : GoalShape → String
  | .equality => "equality"
  | .iff => "iff"
  | .conjunction => "conjunction"
  | .forall => "forall"
  | .exists => "exists"
  | .structure => "structure"
  | .proposition => "proposition"
  | .data => "data"
  | .other => "other"

private def bounded (limit : Nat) (text : String) : String :=
  if text.length ≤ limit then text else (text.take limit).toString ++ "…"

private def pp (expr : Expr) : MetaM String := do
  return (← ppExpr expr).pretty

private def actionKindAndSummary (action : ProofAction) : MetaM (String × String) := do
  match action.payload with
  | .close solver => return ("close", (repr solver).pretty)
  | .structural rule => return ("structural", (repr rule).pretty)
  | .sketch holes => return ("sketch", s!"{holes.size} holes")
  | .proposal proposal =>
      let summary ← match proposal.payload with
        | .cutType type => pp type
        | .libraryApply theoremName => pure (toString theoremName)
        | .equalityMid mid => pp mid
        | .iffMid mid => pp mid
        | .witness value => pp value
        | .structural rule => pure (repr rule).pretty
      return (kindName proposal.kind, summary)

/-- Render only bounded pretty-printed data; raw metavariable state is never exported. -/
def buildRequest
    (snap : GoalSnapshot) (actions : Array ProofAction) (depth : Nat)
    (contextChars : Nat) : MetaM ModelRequest := snap.goalId.withContext do
  let contextChars := max 256 contextChars
  let slots := max 1 (snap.locals.size + actions.size + 1)
  let perItem := max 1 (contextChars / slots)
  let target := bounded perItem (← pp snap.target)
  let mut locals := #[]
  for info in snap.locals do
    let rendered := s!"{info.userName} : {← pp info.type}"
    locals := locals.push (bounded perItem rendered)
  let mut views := #[]
  for action in actions do
    let (kind, summary) ← actionKindAndSummary action
    views := views.push {
      id := toString action.fingerprint
      family := familyName action.family
      kind
      summary := bounded perItem summary
      prior := action.prior
    }
  return {
    requestId := toString snap.fingerprint
    depth
    shape := shapeName snap.shape
    target
    locals
    actions := views
  }

/-- Query within both the per-call timeout and the shared proof-search deadline. -/
def query?
    (snap : GoalSnapshot) (actions : Array ProofAction) (depth : Nat)
    (cfg : ProposeConfig) (budget : Budget) : MetaM (Except String ModelGuidance) := do
  if !cfg.ai then return .error "model guidance is disabled"
  if (← budget.remainingMs) = 0 then return .error "model guidance has no remaining budget"
  let request ← buildRequest snap actions depth cfg.modelContextChars
  let timeoutMs := min (← budget.remainingMs) cfg.modelTimeoutMs
  if timeoutMs = 0 then return .error "model guidance request construction exhausted the budget"
  ModelProvider.query cfg request timeoutMs

/-- Build a bounded interactive request with discrete search feedback and counterfactual views. -/
def buildInteractionRequest
    (snap : GoalSnapshot) (actions : Array ProofAction) (depth round : Nat)
    (feedback : Array SearchFeedback) (frontier : Array FrontierProbe)
    (contextChars : Nat) : MetaM InteractionRequest := do
  let base ← buildRequest snap actions depth contextChars
  return {
    requestId := base.requestId
    round
    depth := base.depth
    shape := base.shape
    target := base.target
    locals := base.locals
    actions := base.actions
    frontier
    feedback
  }

/-- Query one non-scoring continuation round within the shared deadline. -/
def queryInteraction?
    (snap : GoalSnapshot) (actions : Array ProofAction) (depth round : Nat)
    (feedback : Array SearchFeedback) (frontier : Array FrontierProbe)
    (cfg : ProposeConfig) (budget : Budget) :
    MetaM (Except String ModelContinuation) := do
  if !cfg.ai then return .error "interactive model guidance is disabled"
  if (← budget.remainingMs) = 0 then return .error "interactive model guidance has no remaining budget"
  let request ← buildInteractionRequest snap actions depth round feedback frontier cfg.modelContextChars
  let timeoutMs := min (← budget.remainingMs) cfg.modelTimeoutMs
  if timeoutMs = 0 then return .error "interactive request construction exhausted the budget"
  ModelProvider.queryInteraction cfg request timeoutMs
end ModelGuidanceEngine
end ViaLean
