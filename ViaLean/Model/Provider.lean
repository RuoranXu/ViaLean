import ViaLean.Config
import ViaLean.Model.Process

open Lean

namespace ViaLean

namespace ModelProvider

private def systemPrompt : String :=
  "You are a value-and-policy model for Lean proof search. The user message is a JSON object " ++
  "containing a goal and actions already constructed by ViaLean. Return JSON only: " ++
  "{\"value\": number from 0 to 1, \"actions\": [{\"id\": string, \"score\": number from 0 to 1}], " ++
  "\"rationale\": short string}. Score useful next actions highly. Never invent action ids and do not return proof code."

private def interactiveSystemPrompt : String :=
  "You guide Lean proof search without scoring or writing proofs. The user JSON contains " ++
  "kernel-checkable actions and search_feedback produced by model-disabled multi-depth search. " ++
  "Return JSON only: {\"continue\":[{\"id\":string} or {\"index\":number}]," ++
  "\"rationale\":short string}. Choose only listed actions. Use feedback to revise the next choice."
private def openAIRequestJson (cfg : ProposeConfig) (request : ModelRequest) : Json := Json.mkObj [
  ("model", cfg.modelName),
  ("temperature", toJson cfg.modelTemperature),
  ("max_tokens", cfg.modelMaxTokens),
  ("messages", Json.arr #[
    Json.mkObj [("role", "system"), ("content", systemPrompt)],
    Json.mkObj [("role", "user"), ("content", ModelProtocol.requestText request)]
  ])
]

private def openAIInteractionRequestJson
    (cfg : ProposeConfig) (request : InteractionRequest) : Json := Json.mkObj [
  ("model", cfg.modelName),
  ("temperature", toJson cfg.modelTemperature),
  ("max_tokens", cfg.modelMaxTokens),
  ("messages", Json.arr #[
    Json.mkObj [("role", "system"), ("content", interactiveSystemPrompt)],
    Json.mkObj [("role", "user"), ("content", ModelProtocol.interactionRequestText request)]
  ])
]
private def extractOpenAIContent (text : String) : Except String String := do
  let json ← Json.parse text
  let choices ← (← json.getObjVal? "choices").getArr?
  let some first := choices[0]? | throw "API response has no choices"
  let message ← first.getObjVal? "message"
  (← message.getObjVal? "content").getStr?

private def validSecret (secret : String) : Bool :=
  !secret.any (fun c => c = '\n' || c = '\r')

private def escapeCurlConfig (value : String) : String :=
  value.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def queryCommand
    (cfg : ProposeConfig) (request : ModelRequest) (timeoutMs : Nat) :
    IO (Except String ModelGuidance) := do
  let args ← match ModelProtocol.parseArgs cfg.modelCommandArgsJson with
    | .ok args => pure args
    | .error error => return .error s!"invalid modelCommandArgsJson: {error}"
  match ← runBoundedProcess cfg.modelCommand args
      (ModelProtocol.requestText request) timeoutMs cfg.modelMaxResponseChars with
  | .ok output => return ModelProtocol.parseGuidance output.stdout cfg.modelMaxSignals
  | .error error => return .error error

private def queryOpenAI
    (cfg : ProposeConfig) (request : ModelRequest) (timeoutMs : Nat) :
    IO (Except String ModelGuidance) := do
  unless cfg.modelEndpoint.startsWith "http://" || cfg.modelEndpoint.startsWith "https://" do
    return .error "modelEndpoint must use http:// or https://"
  if cfg.modelName.isEmpty then return .error "modelName is empty"
  let secret? ← if cfg.modelApiKeyEnv.isEmpty then pure none else IO.getEnv cfg.modelApiKeyEnv
  if let some secret := secret? then
    unless validSecret secret do return .error "API key contains a newline"
  IO.FS.withTempFile fun configHandle configPath => do
    if let some secret := secret? then
      configHandle.putStrLn s!"header = \"Authorization: Bearer {escapeCurlConfig secret}\""
    configHandle.flush
    let timeoutSec := max 1 ((timeoutMs + 999) / 1000)
    let args := #[
      "--silent", "--show-error", "--fail-with-body",
      "--max-time", toString timeoutSec,
      "--header", "Content-Type: application/json",
      "--config", configPath.toString,
      "--data-binary", "@-",
      cfg.modelEndpoint
    ]
    match ← runBoundedProcess cfg.modelCurlCommand args
        (openAIRequestJson cfg request).compress timeoutMs cfg.modelMaxResponseChars with
    | .error error => return .error error
    | .ok output =>
        match extractOpenAIContent output.stdout with
        | .error error => return .error s!"invalid OpenAI-compatible response: {error}"
        | .ok content => return ModelProtocol.parseGuidance content cfg.modelMaxSignals

private def queryInteractionCommand
    (cfg : ProposeConfig) (request : InteractionRequest) (timeoutMs : Nat) :
    IO (Except String ModelContinuation) := do
  let args ← match ModelProtocol.parseArgs cfg.modelCommandArgsJson with
    | .ok args => pure args
    | .error error => return .error s!"invalid modelCommandArgsJson: {error}"
  match ← runBoundedProcess cfg.modelCommand args
      (ModelProtocol.interactionRequestText request) timeoutMs cfg.modelMaxResponseChars with
  | .ok output => return ModelProtocol.parseContinuation output.stdout cfg.modelMaxSignals
  | .error error => return .error error

private def queryInteractionOpenAI
    (cfg : ProposeConfig) (request : InteractionRequest) (timeoutMs : Nat) :
    IO (Except String ModelContinuation) := do
  unless cfg.modelEndpoint.startsWith "http://" || cfg.modelEndpoint.startsWith "https://" do
    return .error "modelEndpoint must use http:// or https://"
  if cfg.modelName.isEmpty then return .error "modelName is empty"
  let secret? ← if cfg.modelApiKeyEnv.isEmpty then pure none else IO.getEnv cfg.modelApiKeyEnv
  if let some secret := secret? then
    unless validSecret secret do return .error "API key contains a newline"
  IO.FS.withTempFile fun configHandle configPath => do
    if let some secret := secret? then
      configHandle.putStrLn s!"header = \"Authorization: Bearer {escapeCurlConfig secret}\""
    configHandle.flush
    let timeoutSec := max 1 ((timeoutMs + 999) / 1000)
    let args := #[
      "--silent", "--show-error", "--fail-with-body",
      "--max-time", toString timeoutSec,
      "--header", "Content-Type: application/json",
      "--config", configPath.toString,
      "--data-binary", "@-",
      cfg.modelEndpoint
    ]
    match ← runBoundedProcess cfg.modelCurlCommand args
        (openAIInteractionRequestJson cfg request).compress timeoutMs cfg.modelMaxResponseChars with
    | .error error => return .error error
    | .ok output =>
        match extractOpenAIContent output.stdout with
        | .error error => return .error s!"invalid OpenAI-compatible response: {error}"
        | .ok content => return ModelProtocol.parseContinuation content cfg.modelMaxSignals
/-- Query a configured model provider. Errors are values so search can fall back safely. -/
def query
    (cfg : ProposeConfig) (request : ModelRequest) (timeoutMs : Nat) :
    IO (Except String ModelGuidance) := do
  match cfg.modelProvider.trimAscii.toString.toLower with
  | "command" => queryCommand cfg request timeoutMs
  | "replay" => return ModelProtocol.parseGuidance cfg.modelReplayResponse cfg.modelMaxSignals
  | "openai" | "openai-compatible" | "ollama" => queryOpenAI cfg request timeoutMs
  | "none" | "" => return .error "model provider is disabled"
  | other => return .error s!"unknown model provider: {other}"

/-- Query the non-scoring interactive protocol. -/
def queryInteraction
    (cfg : ProposeConfig) (request : InteractionRequest) (timeoutMs : Nat) :
    IO (Except String ModelContinuation) := do
  match cfg.modelProvider.trimAscii.toString.toLower with
  | "command" => queryInteractionCommand cfg request timeoutMs
  | "replay" => return ModelProtocol.parseContinuation cfg.modelReplayResponse cfg.modelMaxSignals
  | "openai" | "openai-compatible" | "ollama" => queryInteractionOpenAI cfg request timeoutMs
  | "none" | "" => return .error "model provider is disabled"
  | other => return .error s!"unknown model provider: {other}"
end ModelProvider
end ViaLean