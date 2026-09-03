import ViaLean.Action
import ViaLean.Frontier
import Lean.Data.Json.FromToJson

open Lean

namespace ViaLean

/-- A serializable view of one kernel-checkable action offered to a model. -/
structure ModelActionView where
  id      : String
  family  : String
  kind    : String
  summary : String
  prior   : Float

deriving Inhabited, Repr

/-- Dense-guidance request sent at every unresolved search node. -/
structure ModelRequest where
  requestId : String
  depth     : Nat
  shape     : String
  target    : String
  locals    : Array String
  actions   : Array ModelActionView

deriving Inhabited, Repr

/-- One kernel-search event returned to an interactive model on the next round. -/
structure SearchFeedback where
  sequence  : Nat
  depth     : Nat
  goal      : String
  actionId  : String
  family    : String
  action    : String := ""
  outcome   : String
  elapsedMs : Nat
  detail    : String := ""

deriving Inhabited, Repr

/-- A non-scoring, multi-round request. Feedback comes only from non-model search. -/
structure InteractionRequest where
  requestId : String
  round     : Nat
  depth     : Nat
  shape     : String
  target    : String
  locals    : Array String
  actions   : Array ModelActionView
  frontier  : Array FrontierProbe := #[]
  feedback  : Array SearchFeedback := #[]

deriving Inhabited, Repr

structure ModelSelection where
  actionId? : Option UInt64 := none
  index?    : Option Nat := none
  probeId?  : Option String := none
  probeIndex? : Option Nat := none

deriving Inhabited, Repr

structure ModelContinuation where
  selections : Array ModelSelection := #[]
  leanCandidates : Array String := #[]
  rationale? : Option String := none

deriving Inhabited, Repr
structure ModelActionSignal where
  actionId : UInt64
  score    : Float

deriving Inhabited, Repr

/-- Untrusted forward signal. It can rank actions but can never close a goal. -/
structure ModelGuidance where
  value        : Float := 0.5
  actionScores : Std.HashMap UInt64 Float := {}
  rationale?   : Option String := none

deriving Inhabited

namespace ModelProtocol

def version : String := "vialean.guidance.v1"
def interactiveVersion : String := "vialean.interactive.v1"

def clamp01 (x : Float) : Float :=
  if x.isNaN || x.isInf then 0.5
  else if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x

def blendScore (base : Float) (signal? : Option Float) (weight : Float) : Float :=
  let weight := clamp01 weight
  match signal? with
  | none => base
  | some signal => (1.0 - weight) * base + weight * clamp01 signal

def ModelGuidance.score? (guidance : ModelGuidance) (id : UInt64) : Option Float :=
  guidance.actionScores.get? id

private def actionToJson (action : ModelActionView) : Json := Json.mkObj [
  ("id", action.id),
  ("family", action.family),
  ("kind", action.kind),
  ("summary", action.summary),
  ("prior", toJson action.prior)
]

def requestToJson (request : ModelRequest) : Json := Json.mkObj [
  ("protocol", version),
  ("request_id", request.requestId),
  ("depth", request.depth),
  ("goal", Json.mkObj [
    ("shape", request.shape),
    ("target", request.target),
    ("locals", toJson request.locals)
  ]),
  ("actions", Json.arr (request.actions.map actionToJson))
]

def requestText (request : ModelRequest) : String :=
  (requestToJson request).compress
private def interactionActionToJson (action : ModelActionView) : Json := Json.mkObj [
  ("id", action.id),
  ("family", action.family),
  ("kind", action.kind),
  ("summary", action.summary)
]
private def frontierToJson (probe : FrontierProbe) : Json := Json.mkObj [
  ("id", probe.id),
  ("perspective", probe.perspective),
  ("operation", probe.operation),
  ("source", probe.source),
  ("result", probe.result),
  ("executable", probe.executable),
  ("goals", toJson probe.goals),
  ("facts", toJson probe.facts),
  ("future", Json.arr (probe.future.map fun view => Json.mkObj [
    ("depth", view.depth),
    ("path", view.path),
    ("goal", view.goal),
    ("signals", toJson view.signals)
  ]))
]
private def feedbackToJson (event : SearchFeedback) : Json := Json.mkObj [
  ("sequence", event.sequence),
  ("depth", event.depth),
  ("goal", event.goal),
  ("action_id", event.actionId),
  ("family", event.family),
  ("action", event.action),
  ("outcome", event.outcome),
  ("elapsed_ms", event.elapsedMs),
  ("detail", event.detail)
]

def interactionRequestToJson (request : InteractionRequest) : Json := Json.mkObj [
  ("protocol", interactiveVersion),
  ("request_id", request.requestId),
  ("round", request.round),
  ("depth", request.depth),
  ("goal", Json.mkObj [
    ("shape", request.shape),
    ("target", request.target),
    ("locals", toJson request.locals)
  ]),
  ("actions", Json.arr (request.actions.map interactionActionToJson)),
  ("frontier", Json.arr (request.frontier.map frontierToJson)),
  ("search_feedback", Json.arr (request.feedback.map feedbackToJson))
]

def interactionRequestText (request : InteractionRequest) : String :=
  (interactionRequestToJson request).compress

/-- Serialize a valid request under an absolute character cap. Low-value history is
removed before local context; if even the minimal request cannot fit, emit `{}`. -/
partial def interactionRequestTextCapped
    (request : InteractionRequest) (maxChars : Nat) : String :=
  let text := interactionRequestText request
  if text.length <= maxChars then text
  else if !request.feedback.isEmpty then
    interactionRequestTextCapped { request with feedback := request.feedback.extract 1 request.feedback.size } maxChars
  else if request.frontier.any (fun probe => !probe.future.isEmpty) then
    interactionRequestTextCapped { request with frontier := request.frontier.map fun probe =>
      { probe with future := #[] } } maxChars
  else if request.frontier.size > 1 then
    interactionRequestTextCapped { request with frontier := request.frontier.extract 0 (request.frontier.size / 2) } maxChars
  else if request.actions.size > 1 then
    interactionRequestTextCapped { request with actions := request.actions.extract 0 (request.actions.size / 2) } maxChars
  else if request.locals.size > 1 then
    interactionRequestTextCapped { request with locals := request.locals.extract 0 (request.locals.size / 2) } maxChars
  else if request.target.length > 64 then
    interactionRequestTextCapped { request with target := (request.target.take (request.target.length / 2)).toString } maxChars
  else if text.length <= maxChars then text
  else if maxChars >= 2 then "{}" else ""

structure PlannerBudgetView where
  remainingMs : Nat
  remainingAtlasWork : Nat
deriving Inhabited, Repr

structure PlannerRootView where
  id : String
  shape : String
  goal : String
deriving Inhabited, Repr

structure PlannerRegionView where
  id : String
  family : String
  size : Nat
  signals : Array String := #[]
  representatives : Array String := #[]
deriving Inhabited, Repr

structure PlannerNodeView where
  id : String
  depth : Nat
  goal : String
  subgoals : Nat := 1
  exactLocal : Bool := false
  contradiction : Bool := false
deriving Inhabited, Repr

structure PlannerTransitionView where
  id : String
  sourceId : String
  targetIds : Array String := #[]
  family : String
  operation : String
  cost : Float := 1.0
  executable : Bool := true
deriving Inhabited, Repr

structure PlannerObservationView where
  transition? : Option String := none
  outcome : String
  failureClass? : Option String := none
deriving Inhabited, Repr

structure PlannerRequestV2 where
  requestId : String
  workspaceVersion : Nat
  budget : PlannerBudgetView
  root : PlannerRootView
  regions : Array PlannerRegionView := #[]
  nodes : Array PlannerNodeView := #[]
  transitions : Array PlannerTransitionView := #[]
  observations : Array PlannerObservationView := #[]
deriving Inhabited, Repr

structure PlannerRegionScore where
  id : String
  score : Float
deriving Inhabited, Repr

structure PlannerTransitionScore where
  id : String
  policy : Float := 0.5
  value : Float := 0.5
  confidence : Float := 0.5
deriving Inhabited, Repr

structure StrategyPlan where
  primaryFamily? : Option String := none
  objective? : Option String := none
deriving Inhabited, Repr

structure ExpansionRequest where
  regionId : String
  extraDepth : Nat := 0
  family? : Option String := none
deriving Inhabited, Repr

structure PlannerThoughtView where
  id : String
  kind : String
  expressionRef : String
  dependencies : Array String := #[]
deriving Inhabited, Repr

structure PlannerResponseV2 where
  rootValue : Float := 0.5
  confidence : Float := 0.5
  preferredRegions : Array PlannerRegionScore := #[]
  transitionScores : Array PlannerTransitionScore := #[]
  strategy : StrategyPlan := {}
  expansionRequests : Array ExpansionRequest := #[]
  thoughts : Array PlannerThoughtView := #[]
  leanCandidates : Array String := #[]
deriving Inhabited, Repr

def plannerVersion : String := "vialean.planner.v2"

private def plannerRegionToJson (region : PlannerRegionView) : Json := Json.mkObj [
  ("id", region.id), ("family", region.family), ("size", region.size),
  ("signals", toJson region.signals), ("representatives", toJson region.representatives)]

private def plannerNodeToJson (node : PlannerNodeView) : Json := Json.mkObj [
  ("id", node.id), ("depth", node.depth), ("goal", node.goal),
  ("signals", Json.mkObj [("subgoals", node.subgoals), ("exact_local", node.exactLocal),
    ("contradiction", node.contradiction)])]

private def plannerTransitionToJson (transition : PlannerTransitionView) : Json := Json.mkObj [
  ("id", transition.id), ("from", transition.sourceId), ("to", toJson transition.targetIds),
  ("family", transition.family), ("operation", transition.operation),
  ("cost", toJson transition.cost), ("executable", transition.executable)]

private def plannerObservationToJson (observation : PlannerObservationView) : Json := Json.mkObj [
  ("transition", observation.transition?.map Json.str |>.getD Json.null),
  ("outcome", observation.outcome),
  ("class", observation.failureClass?.map Json.str |>.getD Json.null)]

def plannerRequestToJson (request : PlannerRequestV2) : Json := Json.mkObj [
  ("version", plannerVersion), ("request_id", request.requestId),
  ("workspace_version", request.workspaceVersion),
  ("budget", Json.mkObj [("remaining_ms", request.budget.remainingMs),
    ("remaining_atlas_work", request.budget.remainingAtlasWork)]),
  ("root", Json.mkObj [("id", request.root.id), ("shape", request.root.shape),
    ("goal", request.root.goal)]),
  ("regions", Json.arr (request.regions.map plannerRegionToJson)),
  ("nodes", Json.arr (request.nodes.map plannerNodeToJson)),
  ("transitions", Json.arr (request.transitions.map plannerTransitionToJson)),
  ("observations", Json.arr (request.observations.map plannerObservationToJson))]

def plannerRequestText (request : PlannerRequestV2) : String :=
  (plannerRequestToJson request).compress

/-- Planner payload hard cap with deterministic semantic degradation. -/
partial def plannerRequestTextCapped (request : PlannerRequestV2) (maxChars : Nat) : String :=
  let text := plannerRequestText request
  if text.length <= maxChars then text
  else if !request.observations.isEmpty then
    plannerRequestTextCapped { request with observations := request.observations.extract 1 request.observations.size } maxChars
  else if request.nodes.size > request.regions.size && request.nodes.size > 1 then
    plannerRequestTextCapped { request with nodes := request.nodes.extract 0 (request.nodes.size / 2) } maxChars
  else if request.transitions.size > 1 then
    plannerRequestTextCapped { request with transitions := request.transitions.extract 0 (request.transitions.size / 2) } maxChars
  else if request.regions.size > 1 then
    plannerRequestTextCapped { request with regions := request.regions.extract 0 (request.regions.size / 2) } maxChars
  else if request.root.goal.length > 64 then
    plannerRequestTextCapped { request with root := { request.root with
      goal := (request.root.goal.take (request.root.goal.length / 2)).toString } } maxChars
  else if maxChars >= 2 then "{}" else ""

private def jsonFloat (json : Json) (field : String) (fallback : Float) : Float :=
  match json.getObjVal? field with
  | .ok value => clamp01 ((fromJson? value : Except String Float).toOption.getD fallback)
  | .error _ => fallback

def parsePlannerResponse (text : String) (maxItems : Nat := 64) : Except String PlannerResponseV2 := do
  let json ← Json.parse text.trimAscii.toString
  let rootValue := jsonFloat json "root_value" 0.5
  let confidence := jsonFloat json "confidence" 0.5
  let mut preferredRegions : Array PlannerRegionScore := #[]
  if let .ok value := json.getObjVal? "preferred_regions" then
    if let .ok items := value.getArr? then
      for item in items.take maxItems do
        if let .ok idJson := item.getObjVal? "id" then
          if let .ok id := idJson.getStr? then
            preferredRegions := preferredRegions.push { id, score := jsonFloat item "score" 0.5 }
  let mut transitionScores : Array PlannerTransitionScore := #[]
  if let .ok value := json.getObjVal? "transition_scores" then
    if let .ok items := value.getArr? then
      for item in items.take maxItems do
        if let .ok idJson := item.getObjVal? "id" then
          if let .ok id := idJson.getStr? then
            transitionScores := transitionScores.push {
              id, policy := jsonFloat item "policy" 0.5
              value := jsonFloat item "value" 0.5
              confidence := jsonFloat item "confidence" confidence }
  let strategy : StrategyPlan := match json.getObjVal? "strategy" with
    | .ok value => {
        primaryFamily? := (value.getObjVal? "primary_family").toOption.bind (·.getStr?.toOption)
        objective? := (value.getObjVal? "objective").toOption.bind (·.getStr?.toOption) }
    | .error _ => ({} : StrategyPlan)
  let mut expansionRequests : Array ExpansionRequest := #[]
  if let .ok value := json.getObjVal? "expansion_requests" then
    if let .ok items := value.getArr? then
      for item in items.take maxItems do
        if let .ok idJson := item.getObjVal? "region_id" then
          if let .ok regionId := idJson.getStr? then
            let extraDepth := (item.getObjVal? "extra_depth").toOption.bind fun v =>
              (fromJson? v : Except String Nat).toOption
            let family? := (item.getObjVal? "family").toOption.bind (·.getStr?.toOption)
            expansionRequests := expansionRequests.push {
              regionId, extraDepth := extraDepth.getD 0, family? }
  let mut thoughts : Array PlannerThoughtView := #[]
  if let .ok value := json.getObjVal? "thoughts" then
    if let .ok items := value.getArr? then
      for item in items.take maxItems do
        let id? := (item.getObjVal? "id").toOption.bind (·.getStr?.toOption)
        let kind? := (item.getObjVal? "kind").toOption.bind (·.getStr?.toOption)
        let ref? := (item.getObjVal? "expression_ref").toOption.bind (·.getStr?.toOption)
        if let (some id, some kind, some expressionRef) := (id?, kind?, ref?) then
          let dependencies := (item.getObjVal? "dependencies").toOption.bind
            (·.getArr?.toOption) |>.map (·.filterMap (·.getStr?.toOption)) |>.getD #[]
          thoughts := thoughts.push { id, kind, expressionRef, dependencies }
  let mut leanCandidates : Array String := #[]
  if let .ok value := json.getObjVal? "lean_candidates" then
    if let .ok items := value.getArr? then
      for item in items.take maxItems do
        let code? := match item.getStr? with
          | .ok code => some code
          | .error _ => (item.getObjVal? "code").toOption.bind (·.getStr?.toOption)
        if let some code := code? then
          unless code.trimAscii.isEmpty do leanCandidates := leanCandidates.push code
  return {
    rootValue := rootValue
    confidence := confidence
    preferredRegions := preferredRegions
    transitionScores := transitionScores
    strategy := strategy
    expansionRequests := expansionRequests
    thoughts := thoughts
    leanCandidates := leanCandidates
  }

private def parseActionId (json : Json) : Except String UInt64 := do
  let idJson ← json.getObjVal? "id"
  let idText ← idJson.getStr?
  let some idNat := idText.toNat?
    | throw s!"invalid action id: {idText}"
  if idNat ≥ UInt64.size then throw "action id exceeds UInt64"
  return UInt64.ofNat idNat

private def parseSignal (json : Json) : Except String ModelActionSignal := do
  let actionId ← parseActionId json
  let score ← fromJson? (← json.getObjVal? "score")
  return { actionId, score := clamp01 score }

private def stripCodeFence (text : String) : String :=
  let text := text.trimAscii.toString
  if text.startsWith "```" then
    let lines := text.splitOn "\n"
    let body := lines.drop 1
    let body := if body.reverse.head?.any (·.trimAscii.toString.startsWith "```") then
      body.reverse.drop 1 |>.reverse
    else body
    String.intercalate "\n" body |>.trimAscii.toString
  else text

private def firstJsonObject? (text : String) : Option String :=
  let rec loop (chars : List Char) (started : Bool) (depth : Nat)
      (inString escaped : Bool) (acc : List Char) : Option String :=
    match chars with
    | [] => none
    | c :: rest =>
        if !started then
          if c = '{' then loop rest true 1 false false [c]
          else loop rest false 0 false false []
        else
          let acc := c :: acc
          if inString then
            if escaped then loop rest true depth true false acc
            else if c = '\\' then loop rest true depth true true acc
            else if c = '"' then loop rest true depth false false acc
            else loop rest true depth true false acc
          else if c = '"' then loop rest true depth true false acc
          else if c = '{' then loop rest true (depth + 1) false false acc
          else if c = '}' then
            if depth = 1 then some (String.ofList acc.reverse)
            else loop rest true (depth - 1) false false acc
          else loop rest true depth false false acc
  loop text.toList false 0 false false []

private def looksLikeGuidance (json : Json) : Bool :=
  (json.getObjVal? "value").isOk || (json.getObjVal? "actions").isOk

private def firstGuidanceJson? (text : String) : Option Json :=
  let rec loop : List Char → Option Json
    | [] => none
    | c :: rest =>
        if c = '{' then
          match firstJsonObject? (String.ofList (c :: rest)) with
          | some objectText =>
              match Json.parse objectText with
              | .ok json => if looksLikeGuidance json then some json else loop rest
              | .error _ => loop rest
          | none => loop rest
        else loop rest
  loop text.toList

/-- Parse the stable provider response. Unknown fields are intentionally ignored. -/
def parseGuidance (text : String) (maxSignals : Nat := 64) : Except String ModelGuidance := do
  let cleaned := stripCodeFence text
  let json ← match Json.parse cleaned with
    | .ok json => pure json
    | .error originalError =>
        match firstGuidanceJson? cleaned with
        | some json => pure json
        | none => throw originalError
  let value := match json.getObjVal? "value" with
    | .ok valueJson => (fromJson? valueJson).toOption.getD 0.5
    | .error _ => 0.5
  let rationale? := match json.getObjVal? "rationale" with
    | .ok rationaleJson => rationaleJson.getStr?.toOption
    | .error _ => none
  let signalJsons := match json.getObjVal? "actions" with
    | .ok actionsJson => actionsJson.getArr?.toOption.getD #[]
    | .error _ => #[]
  let mut scores : Std.HashMap UInt64 Float := {}
  let mut accepted := 0
  for signalJson in signalJsons do
    if accepted ≥ maxSignals then break
    match parseSignal signalJson with
    | .ok signal =>
        let previous := scores.get? signal.actionId
        let score := previous.map (max · signal.score) |>.getD signal.score
        scores := scores.insert signal.actionId score
        accepted := accepted + 1
    | .error _ => pure ()
  return { value := clamp01 value, actionScores := scores, rationale? }

private def parseSelection (json : Json) : Except String ModelSelection := do
  match json.getStr? with
  | .ok idText =>
      let some idNat := idText.toNat? | throw "invalid action id"
      if idNat ≥ UInt64.size then throw "action id exceeds UInt64"
      return { actionId? := some (UInt64.ofNat idNat) }
  | .error _ =>
      let actionId? := match json.getObjVal? "id" with
        | .ok idJson => (parseActionId (Json.mkObj [("id", idJson)])).toOption
        | .error _ => none
      let index? := match json.getObjVal? "index" with
        | .ok indexJson => (fromJson? indexJson : Except String Nat).toOption
        | .error _ => none
      let probeId? := match json.getObjVal? "probe_id" with
        | .ok probeJson => probeJson.getStr?.toOption
        | .error _ => none
      let probeIndex? := match json.getObjVal? "probe_index" with
        | .ok indexJson => (fromJson? indexJson : Except String Nat).toOption
        | .error _ => none
      if actionId?.isNone && index?.isNone && probeId?.isNone && probeIndex?.isNone then
        throw "selection requires id, index, probe_id, or probe_index"
      return { actionId?, index?, probeId?, probeIndex? }

private def looksLikeContinuation (json : Json) : Bool :=
  (json.getObjVal? "continue").isOk ||
  (json.getObjVal? "lean").isOk ||
  (json.getObjVal? "lean_code").isOk ||
  (json.getObjVal? "lean_candidates").isOk

private def firstContinuationJson? (text : String) : Option Json :=
  let rec loop : List Char → Option Json
    | [] => none
    | c :: rest =>
        if c = '{' then
          match firstJsonObject? (String.ofList (c :: rest)) with
          | some objectText =>
              match Json.parse objectText with
              | .ok json => if looksLikeContinuation json then some json else loop rest
              | .error _ => loop rest
          | none => loop rest
        else loop rest
  loop text.toList

/-- Parse an interactive continuation containing Lean candidates and/or optional control choices. -/
def parseContinuation (text : String) (maxSelections : Nat := 16) : Except String ModelContinuation := do
  let cleaned := stripCodeFence text
  let json ← match Json.parse cleaned with
    | .ok json => pure json
    | .error originalError =>
        match firstContinuationJson? cleaned with
        | some json => pure json
        | none => throw originalError
  let choices := match json.getObjVal? "continue" with
    | .ok choicesJson => choicesJson.getArr?.toOption.getD #[]
    | .error _ => #[]
  let rationale? := match json.getObjVal? "rationale" with
    | .ok rationaleJson => rationaleJson.getStr?.toOption
    | .error _ => none
  let mut selections := #[]
  for choice in choices do
    if selections.size ≥ maxSelections then break
    if let .ok selection := parseSelection choice then
      selections := selections.push selection
  let candidateCode? (candidate : Json) : Option String :=
    match candidate.getStr? with
    | .ok code => some code
    | .error _ => match candidate.getObjVal? "code" with
      | .ok codeJson => codeJson.getStr?.toOption
      | .error _ => none
  let mut leanCandidates := #[]
  if let .ok leanJson := json.getObjVal? "lean" then
    if let some code := candidateCode? leanJson then
      unless code.trimAscii.isEmpty do leanCandidates := leanCandidates.push code
  if leanCandidates.size < maxSelections then
    if let .ok leanJson := json.getObjVal? "lean_code" then
      if let some code := candidateCode? leanJson then
        unless code.trimAscii.isEmpty do leanCandidates := leanCandidates.push code
  if let .ok candidatesJson := json.getObjVal? "lean_candidates" then
    if let .ok candidates := candidatesJson.getArr? then
      for candidate in candidates do
        if leanCandidates.size ≥ maxSelections then break
        if let some code := candidateCode? candidate then
          unless code.trimAscii.isEmpty do leanCandidates := leanCandidates.push code
  return { selections, leanCandidates, rationale? }
def parseArgs (text : String) : Except String (Array String) := do
  let json ← Json.parse text
  fromJson? json

end ModelProtocol
end ViaLean
