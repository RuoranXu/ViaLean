# ViaLean

**Persistent neural-symbolic proof search for Lean 4.**

ViaLean is an independent theorem-proving engine that combines structured symbolic search with optional language-model guidance. It maintains a bounded, persistent graph of proof states and verified transitions, explores diverse local futures, and lets a model reason over that evolving proof space instead of limiting it to one-step tactic selection.

The core engine runs fully offline and has no external prover, native extension, FFI, or Lake package dependency. Model-generated plans, intermediate bridges, and Lean candidates remain proposals until Lean accepts them. Every completed proof is checked by the Lean kernel.

## Highlights

- **Persistent Proof Atlas** - proof states, executable transitions, recursive subgoals, intermediate objects, and outcomes are retained in a deduplicated workspace.
- **Dense symbolic lookahead** - bounded search explores normalization, rewriting, elimination, construction, backward reasoning, forward chaining, equality closure, and other complementary local futures.
- **Deep model integration** - models can plan across the Atlas, request targeted expansion, introduce typed conjectures and bridges, or optionally propose Lean code; they are not restricted to choosing an existing action.
- **Local synthesis throughout search** - complete inhabitants and useful partial applications are collected at every visited goal and reused by later search.
- **Budget-aware control** - work, rendering, provider calls, deadlines, and search families have explicit independent bounds.
- **Kernel-checked results** - failed branches are rolled back, unresolved metavariables are rejected, and successful candidates pass final type checking.
- **Optional mathlib integration** - the standalone core remains lightweight while a separate adapter provides mathlib tactics and miniF2F evaluation.

## How it works

```text
Lean goal
   |
   v
Goal identity and persistent workspace
   |
   +-- Symbolic transitions and multi-step local futures
   +-- Premise retrieval and local term synthesis
   +-- Optional model planning, conjectures, and Lean candidates
   |
   v
Budget-aware scheduler and leaf solvers
   |
   v
Lean elaboration and kernel validation
```

Each goal is interned using an alpha-stable semantic key. Executable actions become typed transitions, their subgoals link back into the workspace, and equivalent states merge. The resulting Atlas gives both the symbolic engine and an optional model a shared view of what has been tried, what was learned, and which proof regions remain promising.

Symbolic lookahead is intentionally broad and bounded. ViaLean exposes a compact collection of meaningful nearby futures instead of producing many long, repetitive rollouts. Model responses can connect those futures, request new exploration, create intermediate mathematical objects, or provide a complete or partial Lean proof.

## Quick start

ViaLean uses the Lean toolchain pinned by `lean-toolchain`.

```console
git clone https://github.com/RuoranXu/ViaLean.git
cd ViaLean
lake build
lake test
```

Import the library and invoke `propose` inside a proof:

```lean
import ViaLean

example (P Q : Prop) (hP : P) (hQ : Q) : And P Q := by
  propose
```

`propose?` runs the same search but reports diagnostics without closing the goal. Explicit typed bridges are also available:

```lean
propose via_eq term
propose via_iff proposition
propose via_cut proposition
propose via_witness term
```

## Mathlib integration

Mathlib support lives in a separate Lake project, so applications that use only the ViaLean core do not need to download mathlib.

```console
cd integration/mathlib
lake update
lake exe cache get
lake test
```

The integration pins Lean and mathlib 4.27.0 together with the Google DeepMind Lean 4 miniF2F revision. It provides:

- `mathlibRouter`, combining ViaLean search with a bounded mathlib leaf portfolio;
- `propose_mathlib`, the standard search tactic configured for that router;
- `vialean_dataset_case`, a kernel-checked JSONL evaluation command;
- miniF2F validation and test examples with theorem-answer retrieval disabled.

See [the mathlib integration guide](integration/mathlib/README.md) for setup and dataset details.

## Model integration

External models are optional. ViaLean supports local command adapters, OpenAI-compatible APIs, Ollama or llama.cpp endpoints, and deterministic replay.

| Mode | Role |
|---|---|
| `planner` | Plans over Atlas regions and transitions, requests expansion, creates typed conjectures, and may submit Lean candidates. |
| `interactive` | Receives dense symbolic futures and structured feedback over multiple rounds without requiring scalar action scores. |
| `policy` | Scores existing actions for compatibility with conventional policy/value models. |

A local adapter can be enabled directly from the tactic configuration:

```lean
propose
  (ai := true)
  (modelMode := "interactive")
  (modelProvider := "command")
  (modelCommand := "python")
  (modelCommandArgsJson := "[\"examples/model_adapter.py\"]")
```

The included [command adapter](examples/model_adapter.py) implements the protocol without third-party dependencies. Hosted and local OpenAI-compatible endpoints use the same structured interaction model. See [Model guidance](docs/MODEL_GUIDANCE.md) for protocol schemas, provider configuration, and planner examples.

Raw model-generated Lean tactics are an explicit experimental capability. They require both `modelLeanCode` and `experimentalRawLeanCode`; accepted syntax runs with an independent heartbeat budget on a fresh goal and remains subject to final kernel validation.

## Performance

The current model-free mathlib configuration solves **122 of 244 problems (50.0% pass@1)** on the full miniF2F test split.

| Dataset | Split | Configuration | Solved | Pass@1 |
|---|---|---|---:|---:|
| miniF2F | test | ViaLean symbolic search, no external model | 122 / 244 | **50.0%** |

The repository includes per-case search profiles, isolated mathlib integration, JSONL result records, and matched-compute benchmark modes for reproducing and extending this evaluation. See [Benchmark and corpus notes](benchmarks/README.md).

## Benchmarking and traces

`ViaLean.Benchmark` provides eight evaluation modes ranging from native symbolic search to planner-guided and interactive search. The `vialean.benchmark.v3` record format captures latency, proof attempts, model calls, replans, Atlas size, and Meta work.

Training and analysis traces use the `vialean.training.v3` event stream. Traces contain stable identifiers, decisions, structured outcomes, counts, and failure classes while keeping provider credentials and Lean-internal replay handles out of serialized data.

## Configuration

| Area | Common options |
|---|---|
| Search | `timeoutSec`, `maxDepth`, `maxActionsPerNode`, `rankingMode` |
| Atlas | `atlasMaxNodes`, `atlasMaxTransitions`, `atlasMaxWorkUnits`, `atlasMaxMetaOps`, `atlasMaxRegions` |
| Premises | `library`, `maxRetrievedPremises` |
| Model | `ai`, `modelMode`, `modelProvider`, `modelTimeoutMs`, `modelMaxRounds` |
| Planner | `plannerMaxCalls`, `plannerMaxPayloadChars` |
| Symbolic futures | `frontier`, `frontierMaxProbes`, `frontierMaxPerPerspective` |

All limits are finite and configuration-driven. The implementation contains no Lean release-number checks or per-version behavior branches.

## Project structure

| Path | Purpose |
|---|---|
| `ViaLean/Search.lean` | Main search entry point and orchestration |
| `ViaLean/Workspace.lean` | Persistent proof workspace and Atlas graph |
| `ViaLean/Frontier.lean` | Diverse symbolic probes and local future expansion |
| `ViaLean/Synthesis/Engine.lean` | Local term and partial-application synthesis |
| `ViaLean/Planner/` | Model guidance, conjectures, and planning |
| `ViaLean/Model/` | Provider protocols and process integration |
| `ViaLean/Solver/` | Leaf-solver routing |
| `ViaLeanTest/` | Dependency-free regression and interaction tests |
| `integration/mathlib/` | Mathlib adapter and miniF2F evaluation |
| `benchmarks/` | Evaluation protocol and dataset runner |

For the detailed module map and design invariants, see [VIALEAN_IMPLEMENTATION.md](VIALEAN_IMPLEMENTATION.md).

## Trust model

ViaLean treats symbolic transforms, retrieved premises, model plans, and generated code as proof proposals. A proposal contributes to the final result only after Lean elaborates it into an ordinary proof term with no unresolved metavariables or `sorry` dependencies. Lean's kernel is the final proof authority.

## License

MIT
