import ViaLean.Action
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

def parseArgs (text : String) : Except String (Array String) := do
  let json ← Json.parse text
  fromJson? json

end ModelProtocol
end ViaLean