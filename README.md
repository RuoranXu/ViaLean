# ViaLean

ViaLean is an independent, kernel-checked persistent neural-symbolic co-search engine implemented in Lean 4. Lean continuously builds and verifies a bounded proof workspace; a model can plan over that graph, create typed intermediate bridges, or (in an explicit experimental mode) propose Lean code. Lean's kernel remains the only proof authority.

## Design

The default search path is offline and has no external theorem prover, native extension, FFI, or Lake package dependency. Search runs in `MetaM`, builds ordinary Lean expressions, rolls back failed branches, rejects unresolved metavariables, and validates every completed candidate against the requested target.

The project-owned pipeline provides:

1. strict alpha-stable `GoalKey`s that include let values, collision-confirmed transpositions, explicit work/render/deadline budgets, and AND/OR branch control;
2. structural, equality, equivalence, witness, local-cut, and theorem-name-preserving retrieved-premise application;
3. native contradiction closing, simplification, rewriting, case analysis, introductions, constructors, and premise application;
4. a versioned Proof Workspace/Atlas whose executable transitions and recursive child goals form a deduplicated graph, plus coarse strategy regions for model planning;
5. an ubiquitous LocalSynthesizer that records multiple complete inhabitants and partial local applications at every visited goal;
6. a finite, work-bounded symbolic burst containing heterogeneous probes and diverse multi-step local futures, rather than many long rollouts;
7. cost-aware prior/UCB/planner/hybrid scheduling, a real leaf-solver router, optional aggregate persistence, populated solve statistics, and final proof validation.

## Persistent proof workspace

Every visited goal is interned by strict semantic identity. Each offered or executed action becomes a typed `SymbolicTransitionCandidate`; recursive subgoals are linked back to that transition, repeated states merge, outcomes become structured observations, and Workspace versions drive event-based replanning. Model-created objects remain `speculative` until their own validation/execution succeeds; failed objects are isolated rather than invalidating a whole thought batch.

The model sees compressed regions, representative nodes, executable transition IDs, costs, qualitative signals and structured outcomes—not internal `Expr`, `FVarId`, or replay handles. Planner serialization degrades deterministically and is checked again against `plannerMaxPayloadChars` after final JSON generation.

## Symbolic burst / compatibility frontier

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

Output (`frontierMaxProbes`) and exploration work (`atlasMaxMetaOps`) are separate. Producer work is fairly partitioned across nine strategy families before round-robin output selection; a prolific local-apply family cannot consume the cases/rewrite/constructor share. This concentrates diverse information in a few forward steps instead of spending the budget on many rollouts.

## External model modes

ViaLean supports local command adapters, OpenAI-compatible APIs, Ollama/llama.cpp endpoints, and deterministic replay.

- `modelMode := "planner"` uses `vialean.planner.v2`: policy/value/confidence over Atlas transitions, region strategy, bounded expansion requests, typed conjecture batches, and optional Lean candidates. A typed `expression_ref` may introduce a validated equality/iff bridge, witness, helper cut, or exact term even when the corresponding enumerative proposer is disabled.
- `modelMode := "policy"` keeps the v1 value/action-scoring compatibility path.
- `modelMode := "interactive"` keeps dense non-scoring feedback and finite symbolic futures. It may select existing actions/probes and, when explicitly enabled, submit complete or partial Lean tactics.

Raw model tactic text is untrusted and disabled by default. It runs only when both `modelLeanCode` and `experimentalRawLeanCode` are true. ViaLean accepts an exact allowlist of reviewed core syntax kinds. Trusted routers may add exact parser-node capabilities; the mathlib adapter grants only its reviewed arithmetic/automation tactics. Commands, `run_tac`, evaluation/native execution, option overrides, and ungranted extensions remain rejected. Accepted code runs with an independent heartbeat limit on a fresh goal. Failed candidates restore metavariable state; every successful result still passes the no-`sorry`, no-metavariable final boundary. Provider output is bounded while streamed, and over-limit processes are terminated.

See [Model guidance](docs/MODEL_GUIDANCE.md) for both protocols, or [model_adapter.py](examples/model_adapter.py) for a zero-dependency adapter.

## Tactics

`propose` searches for and closes the current goal. `propose?` reports diagnostics without closing it. Explicit bridge syntax remains available:

```lean
propose via_eq term
propose via_iff proposition
propose via_cut proposition
propose via_witness term
```

Core Atlas bounds are `atlasMaxNodes`, `atlasMaxTransitions`, `atlasMaxWorkUnits`, `atlasMaxMetaOps`, `atlasMaxRenderedChars`, and `atlasMaxRegions`. `maxRetrievedPremises` and `maxActionsPerNode` have distinct meanings. `rankingMode` is one of `.prior`, `.ucb`, `.planner`, or `.hybrid`. Planner bounds include `plannerMaxPayloadChars` and `plannerMaxCalls`; raw code additionally requires `experimentalRawLeanCode := true`.

## Build and test

```console
lake build
lake test
```

The repository has no Lake package dependency. API mode additionally requires `curl`; command mode requires only the configured adapter. Toolchain selection is explicit for reproducible builds, while the implementation contains no Lean release-number checks or per-version branches.

Mathlib support is an isolated integration, so importing the core does not force
downstream projects to download mathlib:

```console
cd integration/mathlib
lake update
lake exe cache get
lake test
```

It pins Lean/mathlib 4.27.0 and the Google DeepMind Lean 4 miniF2F revision, adds a trusted mathlib leaf portfolio, exposes `propose_mathlib`, and emits per-case `vialean.dataset.v1` JSON records.

See [VIALEAN_IMPLEMENTATION.md](VIALEAN_IMPLEMENTATION.md) for the module map and safety invariants.

## Evaluation and traces

ViaLean.Benchmark provides eight matched-compute modes spanning native-only, symbolic actions, flat frontier, graph Atlas, policy, policy+value, planner expansion, and opt-in raw interaction. Results use the stable vialean.benchmark.v3 JSONL schema and include latency, proof attempts, model calls, replans, Atlas size, and Meta work. The root regression corpus in ViaLeanTest/StdDataset.lean is **not miniF2F**: it replays six theorem shapes from the Lean 4 Init/Std sources without importing their proofs or adding mathlib.

The separate `integration/mathlib` suite contains real Lean 4 miniF2F valid/test
statements. It imports only the upstream problem environment, never the files
that declare the target theorems with `sorry`, and disables library retrieval on
the miniF2F cases to prevent answer leakage. Run `lake env lean ViaLeanMathlibTest/MiniF2F.lean` inside that subproject to force the six cases and stream their JSONL records.

On the full 244-problem miniF2F test split, the current mathlib integration solves
122 problems (50.0%) under the repository's local search profiles, up from 112
(45.9%) in the previous internal baseline. This is a kernel-checked, model-free
snapshot rather than a claim about model-assisted performance; machine, timeout,
and model settings should be reported when comparing runs.

Set traceJsonlPath to emit the redacted vialean.training.v3 event stream. Events contain stable IDs, counts, decisions, outcomes, and failure classes; raw goals, local names, API keys, and internal Lean expressions are deliberately excluded. traceMaxEvents bounds the retained stream.

See [Benchmark and corpus notes](benchmarks/README.md) for scope, provenance, and fair-compute rules.

## License

MIT
