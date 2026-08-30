# Model guidance

ViaLean exposes two bounded, untrusted model modes. Both receive rendered Lean state and objects already constructed by ViaLean. Neither accepts proof terms, tactic programs, shell commands, or new executable payloads.

## Interactive mode: diverse finite lookahead

Interactive mode is designed for dense forward signal without scalar scoring or many rollouts:

```lean
propose
  (ai := true)
  (modelMode := "interactive")
  (modelProvider := "openai-compatible")
  (modelEndpoint := "http://127.0.0.1:8080/v1/chat/completions")
  (modelName := "local-model")
  (modelMaxRounds := 4)
  (frontierMaxProbes := 32)
  (frontierForwardDepth := 2)
```

For each unresolved node, ViaLean computes one frontier atlas and reuses it across rounds. Per-perspective quotas are merged round-robin, so repeated rewrites cannot crowd out elimination, construction, forward reasoning, or equality closure.

| Perspective | Finite symbolic lookahead | Executable |
|---|---|---|
| `normalization` | WHNF, target-star simp, context-linked simp | yes |
| `consistency` | local contradiction core | yes |
| `rewrite` | each local equality in both orientations | yes |
| `elimination` | one bounded cases layer and resulting goals | yes |
| `construction` | each constructor and coupled obligations | yes |
| `backward` | one local apply layer and premises required | yes |
| `forward` | typed local application closure up to a small depth | observation only |
| `equality-graph` | kernel-typed two-edge transitive consequences | observation only |

Each interactive round is strict:

1. the model sees the goal, traditional actions, the complete bounded atlas, and previous search feedback;
2. it selects one action (`id`/`index`) or executable probe (`probe_id`/`probe_index`), without returning a score;
3. ViaLean disables model queries for the selected branch;
4. an action runs normally, or a probe is replayed exactly on a fresh metavariable goal;
5. generated subgoals are recursively searched under the shared deadline;
6. success yields a validated proof; failure rolls back and emits depth/goal/action/outcome/timing events for the next round.

Traditional actions may be empty: an executable frontier probe can independently drive the branch. Observation-only probes provide semantic guidance but are rejected if selected for execution.

## Interactive protocol

Request (`vialean.interactive.v1`, abbreviated):

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
  "actions": [],
  "frontier": [
    {
      "id": "74192...",
      "perspective": "elimination",
      "operation": "cases-one-layer",
      "source": "h",
      "result": "branched",
      "executable": true,
      "goals": ["P ⊢ R", "Q ⊢ R"],
      "facts": []
    },
    {
      "id": "91340...",
      "perspective": "forward",
      "operation": "typed-local-closure",
      "source": "local terms",
      "result": "derived",
      "executable": false,
      "goals": [],
      "facts": ["step 1, hp ← ...", "step 2, ... ⟹ R"]
    }
  ],
  "search_feedback": [
    {
      "sequence": 0,
      "depth": 2,
      "goal": "R",
      "action_id": "812...",
      "family": "frontier/rewrite",
      "action": "rewrite-forward/hEq",
      "outcome": "failed",
      "elapsed_ms": 7
    }
  ]
}
```

The interactive wire format intentionally omits action priors and all score fields.

Select by stable ID:

```json
{
  "continue": [{"probe_id": "74192..."}],
  "rationale": "the elimination preview exposes two locally solvable branches"
}
```

Or by request-local array index, useful for replay tests:

```json
{"continue": [{"probe_index": 0}]}
```

The parser accepts an ordered array for provider compatibility, but the controller executes at most one new selection before returning fresh feedback. Unknown, repeated, non-executable, or out-of-range selections are ignored.

## Policy mode

`modelMode := "policy"` remains the compatibility mode. It asks for a goal value and scores only over existing action IDs, clamps scores to `[0, 1]`, uses the goal value as the fallback signal for unscored actions, mixes signals with local priors using `modelWeight`, normalizes by estimated action cost, and executes the reordered actions through normal rollback and validation.

```json
{
  "value": 0.82,
  "actions": [{"id": "92731...", "score": 0.96}],
  "rationale": "prefer the local equality bridge"
}
```

The frontier is not computed in policy mode.

## Providers

### Local command

```lean
propose
  (ai := true)
  (modelMode := "interactive")
  (modelProvider := "command")
  (modelCommand := "python")
  (modelCommandArgsJson := "[\"examples/model_adapter.py\"]")
```

The process is spawned directly without a shell, reads one JSON request from stdin, and writes one JSON response to stdout. Arguments are a JSON array. Stdout is checked incrementally under a hard UTF-8 memory bound, stderr retains only a bounded prefix, and the process is terminated immediately on response overflow or timeout. The included adapter supports both protocols and prefers an unfailed executable frontier probe before traditional actions.

### OpenAI-compatible API

`modelProvider := "openai-compatible"`, `"openai"`, and `"ollama"` use `/v1/chat/completions`, covering hosted APIs and compatible local Ollama/llama.cpp servers. Transport invokes `curl` without a shell.

The optional key is read from the environment variable named by `modelApiKeyEnv` (default `VIALEAN_API_KEY`), rejected if it contains a newline, placed in a temporary curl config, and never included in traces or process arguments.

### Replay

`modelProvider := "replay"` parses `modelReplayResponse` directly for deterministic protocol and proof-search tests.

## Configuration

| Field | Default | Meaning |
|---|---:|---|
| `ai` | `false` | Enable model queries. |
| `modelMode` | `"policy"` | Scored `policy` or non-scoring `interactive`. |
| `modelProvider` | `"none"` | `command`, `openai-compatible`, `ollama`, or `replay`. |
| `modelTimeoutMs` | `1500` | Per-round provider budget, capped by the global deadline. |
| `modelMaxRounds` | `4` | Interactive rounds at one node. |
| `modelMaxFeedbackEvents` | `48` | Feedback tail sent to the model. |
| `frontier` | `true` | Enable the atlas in interactive mode. |
| `frontierMaxProbes` | `32` | Global atlas bound. |
| `frontierMaxPerPerspective` | `4` | Diversity quota per perspective. |
| `frontierMaxChildren` | `6` | Branch fan-out/render/replay bound. |
| `frontierMaxFacts` | `12` | Forward/equality fact bound. |
| `frontierForwardDepth` | `2` | Typed local forward-composition depth. |
| `frontierContextChars` | `16000` | Atlas rendering budget. |
| `modelContextChars` | `12000` | Goal/action rendering budget. |
| `modelMaxResponseChars` | `65536` | Provider response bound. |
| `modelReplayResponse` | `""` | Fixed deterministic response. |

## Privacy and trust

When `ai` is false, no provider process or HTTP request is made. Interactive mode discloses rendered goals, locals, actions, atlas views, and feedback to the configured provider.

The model cannot bypass validation: serialized probes contain no private replay handles, only ViaLean-created executable probes can replay, preview states are rolled back, nested model calls are disabled, unresolved metavariables and `sorryAx` are rejected, and Lean's kernel checks the final expression.
