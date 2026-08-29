# Model guidance

ViaLean treats an external model as an untrusted value-and-policy oracle. The model receives a bounded text view of the current goal and an array of actions already constructed by ViaLean. It returns a goal value and scores for those action IDs. It never returns proof terms, tactics, shell commands, or new action payloads.

## Search integration

For every unresolved node after the cheap native probe:

1. ViaLean builds all enabled structural, equality, equivalence, witness, local-cut, and library-cut actions.
2. The request is bounded by `modelContextChars` and cached by the goal fingerprint.
3. The provider receives at most `modelTimeoutMs`, additionally capped by the global search deadline.
4. Returned scores are clamped to `[0, 1]` and mixed with internal priors using `modelWeight`.
5. The reordered actions run through the normal rollback, validation, composition, and kernel-checking path.

Malformed responses, process errors, HTTP errors, and timeouts are cached as a miss for that node. Search continues without model guidance.

## OpenAI-compatible API

This mode works with hosted APIs and local servers such as Ollama or llama.cpp that implement `/v1/chat/completions`.

```lean
propose
  (ai := true)
  (modelProvider := "openai-compatible")
  (modelEndpoint := "http://127.0.0.1:8080/v1/chat/completions")
  (modelName := "local-model")
  (modelTimeoutMs := 2000)
  (modelWeight := 0.65)
```

`modelProvider := "ollama"` is an alias for the same wire format. The default endpoint is `http://127.0.0.1:11434/v1/chat/completions`.

For authenticated APIs, set an environment variable before invoking Lake or Lean:

```powershell
$env:VIALEAN_API_KEY = "..."
lake test
```

```sh
export VIALEAN_API_KEY='...'
lake test
```

Change `modelApiKeyEnv` when a different variable name is required. ViaLean reads the secret at call time, rejects newline characters, places the authorization header in a temporary file, and never includes it in model traces or process arguments. The temporary file is removed automatically.

The API transport invokes `curl` without a shell. Override `modelCurlCommand` if the executable has a different path.

## Local command provider

A command provider reads exactly one `vialean.guidance.v1` request from stdin and writes exactly one guidance response to stdout. The command is spawned directly, not through a shell.

```lean
propose
  (ai := true)
  (modelProvider := "command")
  (modelCommand := "python")
  (modelCommandArgsJson := "[\"examples/model_adapter.py\"]")
```

Arguments are a JSON array rather than a shell string, so paths and flags are passed without shell expansion. The process is terminated when its timeout expires. Diagnostic stderr is bounded before it can appear in an error trace.

The adapter can call a local Transformers pipeline, llama.cpp binding, inference daemon, or any other runtime. `examples/model_adapter.py` implements the complete transport with only Python's standard library; replace its scoring function with local inference.

## Protocol

Request:

```json
{
  "protocol": "vialean.guidance.v1",
  "request_id": "184467...",
  "depth": 1,
  "goal": {
    "shape": "equality",
    "target": "a = c",
    "locals": ["h₁ : a = b", "h₂ : b = c"]
  },
  "actions": [
    {
      "id": "92731...",
      "family": "equality_local",
      "kind": "equality_mid",
      "summary": "b",
      "prior": 0.9
    }
  ]
}
```

Response:

```json
{
  "value": 0.82,
  "actions": [
    {"id": "92731...", "score": 0.96}
  ],
  "rationale": "the local midpoint splits the equality into two known steps"
}
```

`value`, `actions`, and `rationale` are optional. Duplicate IDs keep their highest score; invalid entries and IDs not present in the request have no effect. Markdown JSON fences and reasoning prefixes such as `<think>…</think>` are accepted for compatibility with chat models.

## Configuration

| Field | Default | Meaning |
|---|---:|---|
| `ai` | `false` | Enable model queries. |
| `modelProvider` | `"none"` | `command`, `openai-compatible`, `ollama`, or `replay`. |
| `modelTimeoutMs` | `1500` | Per-node model budget, capped by the global deadline. |
| `modelWeight` | `0.65` | Mixture weight for returned action scores. |
| `modelMaxSignals` | `16` | Maximum accepted action-score entries. |
| `modelContextChars` | `12000` | Upper bound used while rendering request items. |
| `modelTemperature` | `0.0` | API sampling temperature. |
| `modelMaxTokens` | `512` | API response token limit. |
| `modelMaxResponseChars` | `65536` | Maximum accepted provider stdout size. |
| `modelApiKeyEnv` | `"VIALEAN_API_KEY"` | Environment variable containing an optional API key. |
| `modelReplayResponse` | `""` | Fixed response for deterministic tests and trace replay. |

`deterministic := true` keeps ViaLean's local ordering stable, but it cannot make an external model deterministic. Use temperature zero or `replay` when exact reproducibility matters.

## Privacy and trust

When `ai` is false, no model process or HTTP request is made. When enabled, the pretty-printed goal, local declarations, and candidate summaries are disclosed to the configured provider. Do not enable a remote endpoint for proprietary theorem statements unless that disclosure is acceptable.

Regardless of provider behavior, the model cannot bypass proof validation: only existing action IDs are scoreable, failed branches roll back, unresolved metavariables and `sorryAx` are rejected, and Lean's kernel checks the final expression.