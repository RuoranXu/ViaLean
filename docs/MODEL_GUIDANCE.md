# Model guidance

ViaLean exposes two bounded, untrusted model modes. Policy mode only scores objects already constructed by ViaLean. Interactive mode can additionally propose validated core Lean `by ...`/tactic scripts; it never accepts declarations, commands, shell text, arbitrary metaprograms, or unchecked proofs.

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
  (frontierFutureDepth := 3)
  (frontierFutureWidth := 6)
  (frontierFutureNodes := 24)
```

For each unresolved node, ViaLean computes one frontier atlas and reuses it across rounds. Per-perspective quotas are merged round-robin, so repeated rewrites cannot crowd out elimination, construction, forward reasoning, equality closure, or the deep future view. The `future-graph` recursively mixes several operators at each node and records full local contexts plus qualitative signals. Its default depth/width/node bounds are 3/6/24.

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
| `future-graph` | bounded multi-step intro/simp/apply/constructor/cases/rewrite paths | observation only |

Each interactive round is strict:

1. the model sees the goal, traditional actions, the complete bounded atlas, multi-step future paths, and previous execution feedback;
2. it returns up to `modelMaxCodeCandidates` Lean candidates and may optionally select actions/probes;
3. each candidate is parsed as a `by` proof or tactic sequence, structurally validated, and run on a fresh goal under a separate heartbeat cap;
4. if the candidate leaves goals, ViaLean disables nested model calls and recursively searches those obligations;
5. a complete branch is finalized and checked; a failed branch restores metavariable state;
6. the next model round sees parse/elaboration errors or remaining goals together with their own bounded future paths.

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
      "facts": ["step 1, hp ← ...", "step 2, ... ⟹ R"],
      "future": []
    },
    {
      "id": "future-1",
      "perspective": "future-graph",
      "operation": "bounded-deep-symbolic-search",
      "source": "multi-operator",
      "result": "expanded",
      "executable": false,
      "goals": [],
      "facts": [],
      "future": [
        {
          "depth": 2,
          "path": "root/apply:qr[0]/apply:pq[0]",
          "goal": "p : P, pq : P → Q, qr : Q → R\n⊢ P",
          "signals": ["exact local p closes this node"]
        }
      ]
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
      "elapsed_ms": 7,
      "detail": "remaining_goal[0]: R"
    }
  ]
}
```

The interactive wire format intentionally omits action priors and all score fields. Future paths are observations, not runnable handles.

Return Lean candidates directly:

```json
{
  "lean_candidates": [
    {"code": "by intro h; exact h"},
    {"code": "intro h"}
  ],
  "rationale": "the first closes directly; the second lets symbolic search continue"
}
```

The `continue` field is optional. It remains useful as a fallback:

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

The parser accepts `lean`, `lean_code`, and ordered `lean_candidates` forms. Repeated code, unknown IDs, non-executable probes, and out-of-range selections are ignored. Code candidates run before optional selections in each round.

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
| `modelLeanCode` | `true` | Accept validated core Lean tactic candidates in interactive mode. |
| `modelMaxCodeCandidates` | `4` | Maximum code candidates executed per response. |
| `modelMaxCodeChars` | `12000` | Per-candidate source bound. |
| `modelCodeMaxHeartbeats` | `50000` | Fresh Lean heartbeat allowance per candidate. |
| `frontier` | `true` | Enable the atlas in interactive mode. |
| `frontierMaxProbes` | `32` | Global atlas bound. |
| `frontierMaxPerPerspective` | `4` | Diversity quota per perspective. |
| `frontierMaxChildren` | `6` | Branch fan-out/render/replay bound. |
| `frontierMaxFacts` | `12` | Forward/equality fact bound. |
| `frontierForwardDepth` | `2` | Typed local forward-composition depth. |
| `frontierFutureDepth` | `3` | Maximum recursive future depth. |
| `frontierFutureWidth` | `6` | Maximum successful transforms expanded per node. |
| `frontierFutureNodes` | `24` | Hard total future-node bound. |
| `frontierContextChars` | `16000` | Atlas rendering budget. |
| `modelContextChars` | `12000` | Goal/action rendering budget. |
| `modelMaxResponseChars` | `65536` | Provider response bound. |
| `modelReplayResponse` | `""` | Fixed deterministic response. |

## Privacy and trust

When `ai` is false, no provider process or HTTP request is made. Interactive mode discloses rendered goals, locals, actions, atlas views, and feedback to the configured provider.

The model cannot bypass validation. Model code must parse to a core `by`/tactic tree; syntax containing commands, `run_tac`, evaluation/native execution, `set_option`, macros, syntax quotations, or non-core tactic extensions is rejected before elaboration. Accepted tactics receive a fresh heartbeat budget and metavariable state. Serialized probes contain no private replay handles, nested model calls are disabled, unresolved metavariables and `sorryAx` are rejected, and Lean's kernel checks the final expression.
