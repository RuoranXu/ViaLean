# ViaLean

**Kernel-checked Lean 4 proof search with a diversity-balanced symbolic frontier and optional language-model guidance.**

ViaLean is a research proof-search engine implemented entirely in Lean 4. Instead of asking a model to discover a complete proof through repeated long rollouts, ViaLean constructs a small, heterogeneous atlas of legal symbolic continuations, executes bounded lookahead, and lets either a symbolic scheduler or an external model choose among the resulting proof futures.

The central design goal is simple:

> Make rare but valid proof local strategies visible before asking a model to rank them.

ViaLean provides its own proof-search controller and bounded symbolic frontier. Its default search path is offline, has no Lake package dependencies, and treats Lean's kernel as the only proof authority.

## Why ViaLean?

Formal proofs are combinatorial. A useful route may require an unusual rewrite, a rare theorem application, or a non-obvious case split in exactly the right order. Under finite neural sampling, such a route can remain invisible even when it already exists in the model's latent repertoire.

The frontier emphasizes **strategy diversity**, not merely token-level variation. Independent quotas keep normalization, rewriting, elimination, construction, backward reasoning, forward reasoning, equality closure, and multi-step future paths from crowding one another out.


## Quick start

ViaLean currently targets the toolchain pinned in [`lean-toolchain`](lean-toolchain). From the repository root:

```console
lake build
lake test
```

The core library has no Lake package dependencies. API-backed model guidance additionally requires `curl`; local command guidance only requires the configured adapter process.

Import the library and invoke `propose` at a goal:

```lean
import ViaLean

example (P Q R : Prop) (pq : P → Q) (qr : Q → R) (p : P) : R := by
  propose (timeoutSec := 5)

example (α : Type) (x : α) : ∃ y : α, y = x := by
  propose (timeoutSec := 5)
```

Use `propose?` to inspect diagnostics without closing the goal:

```lean
example (P : Prop) (h : P) : P := by
  propose? (directProbeSec := 0)
  exact h
```

## Proof interfaces

### Automatic search

```lean
propose
propose (timeoutSec := 20) (maxDepth := 3)
```

### Explicit bridges

When you already know a useful intermediate object, keep it explicit:

```lean
propose via_eq middleTerm
propose via_iff middleProposition
propose via_cut intermediateProposition
propose via_witness witnessTerm
```

Each bridge is elaborated against the current goal, validated for progress, and accepted only if the completed proof passes the final trust boundary.

## Optional model guidance

Model use is opt-in with `ai := true`. ViaLean supports deterministic replay, local command adapters, and OpenAI-compatible endpoints such as local Ollama or llama.cpp servers.

### Interactive mode

Interactive mode shows the model the current goal, legal actions, the symbolic atlas, bounded future paths, and previous execution feedback. The model may return validated Lean tactic candidates or select an executable action/probe.

```lean
propose
  (ai := true)
  (modelMode := "interactive")
  (modelProvider := "command")
  (modelCommand := "python")
  (modelCommandArgsJson := "[\"examples/model_adapter.py\"]")
  (modelMaxRounds := 4)
```

A partial tactic is useful: ViaLean executes it on a fresh goal, then lets ordinary model-disabled symbolic search solve the remaining obligations.

### Policy mode

Policy mode asks the model to score only actions already constructed by ViaLean. The scores are combined with local priors and action costs; the controller still owns execution, rollback, and validation.

See [`docs/MODEL_GUIDANCE.md`](docs/MODEL_GUIDANCE.md) for the JSON protocols, provider configuration, safety rules, and a complete interactive example. A zero-dependency adapter is available at [`examples/model_adapter.py`](examples/model_adapter.py).

## Configuration

Frequently used controls:

| Area | Fields |
| --- | --- |
| Search | `timeoutSec`, `maxDepth`, `maxCandidates`, `maxCandidatesPerFamily` |
| Native solver | `nativeMaxDepth`, `nativeMaxApplications`, `nativeMaxCaseBranches` |
| Frontier | `frontierMaxProbes`, `frontierMaxPerPerspective`, `frontierMaxChildren`, `frontierMaxFacts` |
| Future atlas | `frontierForwardDepth`, `frontierFutureDepth`, `frontierFutureWidth`, `frontierFutureNodes` |
| Model loop | `modelMode`, `modelProvider`, `modelTimeoutMs`, `modelMaxRounds`, `modelMaxFeedbackEvents` |
| Model tactics | `modelLeanCode`, `modelMaxCodeCandidates`, `modelMaxCodeChars`, `modelCodeMaxHeartbeats` |
| Scheduling | `ucb`, `ucbExploration`, `ucbPriorWeight`, `persistentStatsPath` |

All fields and defaults are defined in [`ViaLean/Config.lean`](ViaLean/Config.lean).

## Architecture

| Module | Responsibility |
| --- | --- |
| `ViaLean/Frontier.lean` | Multi-perspective probes, bounded future paths, and replay handles |
| `ViaLean/Search.lean` | AND/OR control, scheduling, model interaction, replay, rollback, and completion |
| `ViaLean/NativeSolver.lean` | Independent bounded leaf solver |
| `ViaLean/Model/` | Protocols, provider transports, process bounds, and request rendering |
| `ViaLean/Proposers/` | Structural, equality, iff, witness, local, library, and cut proposals |
| `ViaLean/Validate.lean` | Proposal validation and progress checks |
| `ViaLean/Tactic.lean` | `propose`, `propose?`, and explicit bridge syntax |
| `ViaLeanTest/` | Search, frontier, protocol, replay, integration, and safety regressions |

For a deeper implementation map and invariants, read [`VIALEAN_IMPLEMENTATION.md`](VIALEAN_IMPLEMENTATION.md).

## Trust and privacy

ViaLean never treats a model response as a proof.

- Completed candidates are instantiated, inferred, and checked against the requested target.
- Proofs containing `sorryAx` or unresolved metavariables are rejected.
- Preview and failed replay branches restore metavariable state.
- Model code is restricted to validated core Lean proof/tactic syntax.
- Commands, `run_tac`, native/evaluation tactics, option overrides, macros, syntax quotations, and non-core tactic extensions are rejected.
- Every accepted model tactic runs with a fresh goal, source-size limit, candidate-count limit, and heartbeat budget.
- When model guidance is disabled, no provider process or HTTP request is made.

If model guidance is enabled, rendered goals, local hypotheses, actions, frontier views, and feedback are sent to the configured provider. Choose that provider according to your privacy requirements.

## Project status

ViaLean is a research prototype. Its search procedures and safety boundaries are tested in this repository, but benchmark claims and large-scale experimental results are intentionally not stated here until the corresponding evaluation artifacts are available.

Contributions are welcome, especially around frontier recall, premise retrieval, model adapters, matched-compute evaluation, and regression cases that require uncommon proof strategies. Please run `lake test` before opening a change.

## License

[MIT](LICENSE)
