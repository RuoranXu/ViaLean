# ViaLean

ViaLean is an independent, kernel-checked proof-search engine implemented in Lean 4. It combines bounded native transformations, compositional proof actions, and optional external-model guidance while keeping Lean's kernel as the only proof authority.

## Design

The default search path is offline and has no external theorem prover, native extension, FFI, or Lake package dependency. Search runs in `MetaM`, builds ordinary Lean expressions, rolls back failed branches, rejects unresolved metavariables, and validates every completed candidate against the requested target.

The project-owned search pipeline provides:

1. bounded goal snapshots, fingerprints, budgets, and AND/OR branch control;
2. structural, equality, equivalence, witness, local-cut, and library-cut actions;
3. native contradiction closing, simplification and hypothesis rewriting, equality-driven normalization, propositional case analysis, introductions, constructors, and premise application;
4. optional stable ordering or UCB scheduling;
5. proof composition followed by final target validation.

External models never submit proof terms or executable tactic text. They can only refer to actions already constructed by ViaLean. Unknown IDs, malformed JSON, process/API failure, timeout, and missing credentials safely fall back to native search.

## External model modes

ViaLean supports local command adapters, OpenAI-compatible APIs, Ollama/llama.cpp endpoints, and deterministic replay.

- `modelMode := "policy"` asks for value/action scores and mixes them with ViaLean's priors.
- `modelMode := "interactive"` does not accept scores. Each model round selects one existing action; ViaLean then disables model calls, performs real multi-depth native search, and returns bounded depth/action/outcome/timing events before the next model round.

The interactive loop therefore supplies dense forward context without treating an unverifiable model number as proof progress.

See [Model guidance](docs/MODEL_GUIDANCE.md) for both wire protocols and configuration, or [model_adapter.py](examples/model_adapter.py) for a zero-dependency adapter supporting both modes.

## Tactics

`propose` searches for and closes the current goal. `propose?` reports diagnostics without closing it. Explicit bridge syntax is available when an intermediate object is known:

```lean
propose via_eq term
propose via_iff proposition
propose via_cut proposition
propose via_witness term
```

Core fields include `timeoutSec`, `directProbeSec`, `candidateProbeSec`, `maxDepth`, `nativeMaxDepth`, `nativeMaxApplications`, `nativeTransforms`, `nativeCases`, `nativeMaxCaseBranches`, `structural`, `cuts`, `equalityBridge`, `iffBridge`, `witnesses`, `library`, `ucb`, `deterministic`, and `trace`.

## Build and test

```console
lake build
lake test
```

The repository has no Lake package dependency. API mode additionally requires a `curl` executable; command mode requires only the configured adapter. Toolchain selection remains explicit for reproducible builds, while the implementation contains no Lean release-number checks or per-version branches.

See [VIALEAN_IMPLEMENTATION.md](VIALEAN_IMPLEMENTATION.md) for the module map and safety invariants.

## License

MIT