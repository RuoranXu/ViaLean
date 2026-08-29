# ViaLean

ViaLean is a small, kernel-checked proof-search engine implemented in Lean 4. It combines bounded native proof search with explicit bridge actions and optional dense model guidance.

## Design

The default search path is offline and has no external theorem-prover, native-extension, FFI, or package dependency. Search runs in `MetaM`, builds ordinary Lean expressions, and validates every candidate against the requested target before assigning the original goal. Lean's kernel remains the final authority.

The search pipeline uses project-owned data structures:

1. `GoalSnapshot` captures the target and local context.
2. proposal providers construct bounded, kernel-checkable actions.
3. an optional model supplies a value estimate and scores those existing actions at every unresolved node.
4. the controller combines model signals, local priors, and optional UCB statistics.
5. the native leaf solver handles introductions, constructors, local hypotheses, and premises.
6. successful child proofs are composed and checked at the final trust boundary.

A model cannot submit a proof or invent an executable action. Unknown action IDs are ignored. Provider failure, malformed JSON, timeout, or missing credentials falls back to native search.

## Dense model guidance

Model support is opt-in and covers OpenAI-compatible APIs, local Ollama/llama.cpp servers, shell-free JSON/stdin command adapters, and deterministic replay. API keys are read from an environment variable and never placed in Lean source.

See [Model guidance](docs/MODEL_GUIDANCE.md) for configuration and the wire protocol, or [model_adapter.py](examples/model_adapter.py) for a zero-dependency local adapter.

## Tactics

`propose` searches for and closes the current goal. `propose?` runs diagnostics without closing it. Explicit bridge syntax is available when the intended intermediate object is known:

```lean
propose via_eq term
propose via_iff proposition
propose via_cut proposition
propose via_witness term
```

Core configuration fields include `timeoutSec`, `directProbeSec`, `candidateProbeSec`, `maxDepth`, `nativeMaxDepth`, `nativeMaxApplications`, `structural`, `cuts`, `equalityBridge`, `iffBridge`, `witnesses`, `library`, `ucb`, `deterministic`, and `trace`. Model fields are documented separately.

## Build and test

```console
lake build
lake test
```

The repository has no Lake package dependency. API guidance additionally requires a `curl` executable; command guidance requires only the configured adapter process. The implementation does not inspect a Lean version string or branch on a release number.

See [VIALEAN_IMPLEMENTATION.md](VIALEAN_IMPLEMENTATION.md) for the module map and safety invariants.

## License

MIT