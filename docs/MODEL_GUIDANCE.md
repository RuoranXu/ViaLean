# Model guidance

ViaLean exposes two model modes over the same bounded, untrusted transport. Both modes receive only a rendered goal, local declarations, and actions already constructed by ViaLean. Neither mode accepts proof terms, tactic programs, shell commands, or new action payloads.

## Interactive mode: search feedback, no scores

This mode is intended for iterative generation with dense forward signals:

```lean
propose
  (ai := true)
  (modelMode := "interactive")
  (modelProvider := "openai-compatible")
  (modelEndpoint := "http://127.0.0.1:8080/v1/chat/completions")
  (modelName := "local-model")
  (modelMaxRounds := 4)
  (modelMaxFeedbackEvents := 48)
```

Each round is strictly interleaved:

1. the model sees the current goal, available action IDs, and bounded previous `search_feedback`;
2. it selects one listed action by ID or array index, without a score;
3. ViaLean disables model queries for that branch and runs its normal multi-depth search;
4. every attempted controller action records its search depth, target, family, result, and elapsed time;
5. after failure, the next model round receives those discrete events and can revise its continuation.

A successful branch is validated and returned immediately. Unknown or repeated selections are ignored. Empty selections, malformed output, provider errors, and exhausted budgets return control to ViaLean's ordinary native ordering.

Interactive request (`vialean.interactive.v1`):

```json
{
  "protocol": "vialean.interactive.v1",
  "request_id": "184467...",
  "round": 1,
  "depth": 0,
  "goal": {
    "shape": "proposition",
    "target": "R",
    "locals": ["h : P ∨ Q", "hp : P → R", "hq : Q → R"]
  },
  "actions": [
    {
      "id": "92731...",
      "family": "structural",
      "kind": "structural",
      "summary": "..."
    }
  ],
  "search_feedback": [
    {
      "sequence": 0,
      "depth": 2,
      "goal": "R",
      "action_id": "812...",
      "family": "local_cut",
      "action": "cut/local-hypothesis",
      "outcome": "failed",
      "elapsed_ms": 7
    }
  ]
}
```

Interactive response:

```json
{
  "continue": [{"id": "92731..."}],
  "rationale": "the failed cut suggests expanding the disjunction"
}
```

`{"index": 0}` is also accepted. Although the parser accepts an ordered array for provider compatibility, the controller attempts at most one new selection before returning fresh search feedback.

## Policy mode: optional score mixing

`modelMode := "policy"` is the default compatibility mode. For every unresolved node after the cheap native probe, ViaLean asks for a goal value and scores over existing action IDs. Scores are clamped to `[0, 1]`, mixed with local priors using `modelWeight`, and then executed through the same rollback and validation path.

```lean
propose
  (ai := true)
  (modelMode := "policy")
  (modelProvider := "openai-compatible")
  (modelEndpoint := "http://127.0.0.1:8080/v1/chat/completions")
  (modelName := "local-model")
  (modelWeight := 0.65)
```

Policy response (`vialean.guidance.v1`):

```json
{
  "value": 0.82,
  "actions": [{"id": "92731...", "score": 0.96}],
  "rationale": "prefer the local equality bridge"
}
```

Duplicate IDs keep their highest score. Invalid and unknown IDs have no effect.

## Providers

### Local command

The command is spawned directly without a shell. It reads one request from stdin and writes one response to stdout.

```lean
propose
  (ai := true)
  (modelMode := "interactive")
  (modelProvider := "command")
  (modelCommand := "python")
  (modelCommandArgsJson := "[\"examples/model_adapter.py\"]")
```

Arguments are a JSON array, so paths and flags are not shell-expanded. The process is terminated at its timeout, stdout is size-bounded, and diagnostic stderr is truncated. The included adapter dispatches on the `protocol` field and demonstrates both modes using only Python's standard library.

### OpenAI-compatible API and local servers

`modelProvider := "openai-compatible"`, `"openai"`, and `"ollama"` use `/v1/chat/completions`. This covers hosted APIs and local compatible servers such as Ollama and llama.cpp. Requests use `curl` without a shell.

For authentication, set the environment variable named by `modelApiKeyEnv` (default `VIALEAN_API_KEY`). The secret is read at call time, rejected if it contains a newline, placed in a temporary curl config file, and never included in model traces or process arguments.

### Replay

`modelProvider := "replay"` parses `modelReplayResponse` directly. It is useful for deterministic protocol and proof-search tests.

## Configuration

| Field | Default | Meaning |
|---|---:|---|
| `ai` | `false` | Enable model queries. |
| `modelMode` | `"policy"` | `policy` score mixing or non-scoring `interactive` feedback. |
| `modelProvider` | `"none"` | `command`, `openai-compatible`, `ollama`, or `replay`. |
| `modelTimeoutMs` | `1500` | Per-round provider budget, capped by the global deadline. |
| `modelMaxRounds` | `4` | Maximum interactive rounds at one search node. |
| `modelMaxFeedbackEvents` | `48` | Tail of discrete events included in an interactive request. |
| `modelWeight` | `0.65` | Policy-only mixture weight for action scores. |
| `modelMaxSignals` | `16` | Maximum accepted scores or continuation selections. |
| `modelContextChars` | `12000` | Bound while rendering goal/action context. |
| `modelTemperature` | `0.0` | API sampling temperature. |
| `modelMaxTokens` | `512` | API response token limit. |
| `modelMaxResponseChars` | `65536` | Maximum provider stdout/API content size. |
| `modelApiKeyEnv` | `"VIALEAN_API_KEY"` | Environment variable for an optional API key. |
| `modelReplayResponse` | `""` | Fixed response for deterministic tests. |

## Privacy and trust

When `ai` is false, no model process or HTTP request is made. When enabled, rendered goals, local declarations, actions, and (in interactive mode) search events are disclosed to the configured provider.

Provider behavior cannot bypass proof validation: only existing actions can execute, model-selected branches run with further model calls disabled, failed branches roll back, unresolved metavariables and `sorryAx` are rejected, and Lean's kernel checks the final expression.