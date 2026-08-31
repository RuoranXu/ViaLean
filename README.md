# ViaLean

ViaLean combines bounded native transformations, a diversity-balanced symbolic frontier, compositional proof actions, and optional external-model guidance while keeping Lean's kernel as the only proof authority.

## Design

The default search path is offline and has no external theorem prover, native extension, FFI, or Lake package dependency. Search runs in `MetaM`, builds ordinary Lean expressions, rolls back failed branches, rejects unresolved metavariables, and validates every completed candidate against the requested target.

The project-owned pipeline provides:

1. bounded goal snapshots, fingerprints, budgets, and AND/OR branch control;
2. structural, equality, equivalence, witness, local-cut, and theorem-name-preserving retrieved-premise application;
3. native contradiction closing, simplification, rewriting, case analysis, introductions, constructors, and premise application;
4. a finite symbolic frontier containing heterogeneous probes plus a bounded multi-step future graph, rather than many long rollouts;
5. cost-aware stable/UCB scheduling, optional aggregate scheduler persistence, populated solve statistics, and final proof validation.

## Symbolic frontier atlas

In interactive mode, ViaLean computes the atlas once per unresolved node and reuses it across model rounds. Alongside the one-layer executable probes, a `future-graph` probe expands a small width/depth-bounded tree of intro, simplification, backward application, construction, elimination, and bidirectional rewrite paths. Every future node includes its full bounded local context, target, path, depth, and qualitative opportunities such as exact closure, rewrite sources, constructors, or backward premises.

Independent quotas preserve diversity across:

- target/context normalization;
- contradiction cores;
- forward and reverse equality rewriting;
- one-layer eliminator branches;
- constructor obligations;
- backward local-theorem application;
- bounded typed forward chaining;
- two-edge equality closure;
- multi-operator symbolic paths, by default depth 3, width 6, and 24 total nodes.

Each probe exposes rendered goals, derived facts, or future paths, never a scalar progress score. Every branch rendering keeps its target and bounded newest-first local context. Executable probes can be selected by `probe_id` or `probe_index`. ViaLean replays the selected transform on a fresh goal, disables nested model calls, recursively solves only the exposed obligations, and either extracts a kernel-checkable proof or rolls the whole branch back. Observation-only forward/future views remain guidance and cannot pretend to be proof steps.

The atlas is bounded by global probe count, per-perspective quota, children per probe, facts, forward depth, rendered characters, and the shared proof-search deadline. This concentrates diverse information in a few forward steps instead of spending the budget on many rollouts.

## External model modes

ViaLean supports local command adapters, OpenAI-compatible APIs, Ollama/llama.cpp endpoints, and deterministic replay.

- `modelMode := "policy"` asks for value/action scores and mixes them with ViaLean's priors.
- `modelMode := "interactive"` accepts no score. Each round may submit several Lean `by ...`/tactic candidates and may optionally select an existing action or executable frontier probe. A complete model tactic can close the goal; a partial tactic exposes obligations that ordinary symbolic search continues under the shared deadline. The next round receives errors, open goals, their deep future paths, and action/probe outcomes.

Model tactic text is untrusted. ViaLean accepts only a validated core Lean proof-tactic syntax tree, rejects commands, `run_tac`, evaluation/native execution, option overrides, macros, and non-core tactic extensions, and runs it with an independent heartbeat limit on a fresh goal. Failed candidates restore metavariable state; all successful results still pass the no-`sorry`, no-metavariable final proof boundary. Provider output is bounded while streamed, and over-limit processes are terminated.

See [Model guidance](docs/MODEL_GUIDANCE.md) for both protocols, or [model_adapter.py](examples/model_adapter.py) for a zero-dependency adapter.

## Tactics

`propose` searches for and closes the current goal. `propose?` reports diagnostics without closing it. Explicit bridge syntax remains available:

```lean
propose via_eq term
propose via_iff proposition
propose via_cut proposition
propose via_witness term
```

Core frontier fields are `frontier`, `frontierMaxProbes`, `frontierMaxPerPerspective`, `frontierMaxChildren`, `frontierMaxFacts`, `frontierForwardDepth`, `frontierFutureDepth`, `frontierFutureWidth`, `frontierFutureNodes`, and `frontierContextChars`. Model-code bounds are `modelLeanCode`, `modelMaxCodeCandidates`, `modelMaxCodeChars`, and `modelCodeMaxHeartbeats`. Native and controller bounds include `timeoutSec`, `maxDepth`, `nativeMaxDepth`, `nativeMaxApplications`, and `nativeMaxCaseBranches`.

## Build and test

```console
lake build
lake test
```

The repository has no Lake package dependency. API mode additionally requires `curl`; command mode requires only the configured adapter. Toolchain selection is explicit for reproducible builds, while the implementation contains no Lean release-number checks or per-version branches.

See [VIALEAN_IMPLEMENTATION.md](VIALEAN_IMPLEMENTATION.md) for the module map and safety invariants.

## License

MIT
