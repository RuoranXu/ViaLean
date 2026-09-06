# ViaLean implementation

## Scope

ViaLean is an independent Lean 4 proof-search library. Its leaf solver, symbolic frontier, bridge search, scheduling, validation, optional model guidance, tracing, and tactic frontend are implemented in this repository with ordinary Lean metaprogramming APIs.

The engine is deliberately bounded. V3 maintains one versioned Proof Workspace: Lean performs frequent symbolic ticks and local synthesis, while sparse neural epochs plan over compressed graph regions and may add independently validated intermediate objects. It searches diverse, deep local futures instead of launching many long rollouts.

## Search model

A node owns a strict `GoalKey`, snapshot, depth, signals and status. `GoalKey` includes ordered local kinds, types, let values and target; names are alpha-normalized and equal hashes still require structural confirmation. Typed actions become executable Atlas transitions, recursive goals link back as children, and repeated goals merge as transpositions. Retrieved library candidates retain their declaration names and replay by applying that exact theorem.

At every node, `LocalSynthesizer` enumerates multiple exact inhabitants plus partial local applications and their gaps. This lane does not depend on a model. `LeafRouter` is the only direct leaf-solver entry used by the controller and applies one shared budget across registered backends.

The atlas separates symbolic perspectives so one prolific family cannot dominate:

- weak-head, target-star, and context normalization;
- local contradiction closure;
- each equality in both rewrite orientations;
- one-layer elimination of bounded inductive propositions;
- each target constructor and its coupled obligations;
- backward application of local declarations;
- typed local forward closure up to `frontierForwardDepth`;
- kernel-typed two-edge equality transitivity;
- recursive multi-operator paths combining intro, simplification, apply, constructors, cases, and rewrites.

Preview tactics run under saved metavariable states and retain rendered strings only. Branch strings preserve the target plus bounded newest-first local declarations introduced by elimination and simplification. Executable probes also retain private stable replay handles (`FVarId` or constructor name), which are never serialized. When selected, the controller creates a fresh goal, replays exactly that operation, disables nested model queries, recursively solves the generated metavariables, and extracts the completed root assignment. Failure restores the complete branch while IO feedback remains available for the next model round.

The observation-only `future-graph` recursively explores several successful transforms per node. It records each node's depth, operator path, full bounded goal state, and qualitative signals rather than a progress score. A shared node counter, per-node width, recursion depth, branch fan-out, rendered-character budget, cycle fingerprints, and the global deadline bound the graph.

Planner v2 is not limited to action selection. It returns policy/value/confidence, region strategy and typed thought batches. A thought can introduce an exact term, helper cut, equality/iff bridge, or witness by referencing a current local/environment constant. Each thought is resolved and validated separately; only a validated proposal enters the Atlas. Optional complete or partial Lean scripts remain available behind the explicit `experimentalRawLeanCode` gate and exact syntax-kind allowlist.

The native solver independently supports exact hypotheses, reflexivity, `True`, contradiction, simplification/rewrite normalization, dependent introductions, constructors, bounded propositional cases, local/global premise application, and recursive subgoal solving.

## Bounds

- `frontierMaxProbes`: compatibility-view output size, not work.
- `atlasMaxNodes`, `atlasMaxTransitions`, `atlasMaxWorkUnits`, `atlasMaxMetaOps`: internal graph/exploration limits.
- `atlasMaxRenderedChars`, `atlasMaxRegions`, `plannerMaxPayloadChars`: representation limits and final JSON hard cap.
- `frontierMaxPerPerspective`: quota before round-robin merging.
- `frontierMaxChildren`: maximum displayed or replayed branch fan-out.
- `frontierMaxFacts`: maximum forward/equality facts.
- `frontierForwardDepth`: typed forward-composition depth.
- `frontierFutureDepth`, `frontierFutureWidth`, `frontierFutureNodes`: recursive future graph bounds.
- `frontierContextChars`: rendering budget for atlas items.
- `modelMaxRounds` and `modelMaxFeedbackEvents`: interaction bounds.
- `modelMaxCodeCandidates`, `modelMaxCodeChars`, and `modelCodeMaxHeartbeats`: model tactic bounds.
- `nativeMaxDepth`, `nativeMaxApplications`, and the shared deadline: recursive execution bounds.

The shared deadline is checked in controller and frontier loops, recomputed after request rendering, passed to native/model processes, and installed as a Lean Core cancellation token so cooperative expensive meta operations terminate when the wall-clock budget expires.

## Modules

- `ViaLean/Config.lean`: search, frontier, and provider configuration.
- `ViaLean/GoalKey.lean`, `Goal.lean`: single strict state identity implementation and snapshots.
- `ViaLean/Symbolic.lean`: unified operation/family/origin transition IR.
- `ViaLean/Atlas/Types.lean`, `Workspace.lean`: executable graph, regions, versioning, thought objects and structured observations.
- `ViaLean/Synthesis/Local.lean`: ubiquitous multiple/partial inhabitant discovery.
- `ViaLean/Proposal.lean`, `Action.lean`: compatibility adapters into the symbolic IR.
- `ViaLean/Frontier.lean`: bounded multi-perspective previews, recursive future paths, and private replay handles.
- `ViaLean/NativeSolver.lean`: independent bounded leaf solver.
- `ViaLean/Model/Protocol.lean`: planner v2 plus policy/interactive v1 compatibility JSON and hard-capped serialization.
- `ViaLean/Model/Process.lean`: shell-free process execution, streaming output bounds, and timeout termination.
- `ViaLean/Model/Provider.lean`: command, replay, and OpenAI-compatible transports.
- `ViaLean/Model/Guidance.lean`: bounded request rendering.
- `ViaLean/Planner/Guidance.lean`, `Planner/Conjecture.lean`: Atlas compression, planner decisions and independently validated open-world candidates.
- `ViaLean/Search/State.lean`, `Search/Replan.lean`: persistent controller state and semantic event-driven replanning.
- `ViaLean/Search/Decision.lean`, `Search/Replay.lean`: ranking/failure decisions and inert ID/index replay resolution.
- `ViaLean/Search/Execute.lean`, `Search/Controller.lean`: transactional Meta execution and one cancellation deadline over the full search.
- `ViaLean/Search/ModelCode.lean`: the experimental raw-code parser and exact syntax allowlist.
- `ViaLean/Search.lean`: AND/OR orchestration over the split services.
- `ViaLean/Benchmark.lean`, `Trace.lean`: matched-compute ablations and redacted stable JSONL events.
- `ViaLean/Compose.lean`, `Validate.lean`: proof construction and trust boundary.
- `ViaLean/Tactic.lean`: `propose` and `propose?`.
- `ViaLeanTest/`: regression, frontier diversity, protocol, replay, and safety tests.
- `integration/mathlib/`: isolated mathlib/Lean 4 miniF2F package, trusted math
  tactic leaf router, `propose_mathlib`, and non-leaking benchmark smoke tests.

## Safety invariants

1. A returned proof contains no unresolved synthetic metavariables.
2. Every returned expression is checked against the requested target.
3. Preview and failed replay branches restore their metavariable state.
4. Search never accepts `sorry`/`admit`, unresolved holes, declarations, commands, native execution, or arbitrary model metaprograms.
5. Raw model tactics are off by default; the compatibility mode uses an exact reviewed syntax-kind allowlist and rejects `run_tac`, evaluation/native tactics, option overrides, macros, syntax quotations, and extensions.
6. Every accepted model tactic runs on a fresh goal with a source-size bound, candidate-count bound, and fresh nonzero heartbeat cap.
7. Model-generated subgoals and selected replay disable nested model calls.
8. Observation-only probes and future paths cannot close a goal.
9. Provider failures, malformed code, and malformed selections degrade to ordinary search.
10. Provider calls, frontier expansion, leaf routing and recursive solving share the global deadline; output and work budgets are distinct.
11. Planner requests obey a hard final serialized payload cap, and replanning is triggered by Workspace version changes rather than blind retry rounds.
12. The original goal is assigned only after complete candidate validation.

## Compatibility policy

The package has no Lake dependencies and no version-specific runtime linkage. It uses Lean's metaprogramming surface without release-number tests or per-version branches. Toolchain selection remains explicit for reproducible builds; API transport uses the external `curl` executable rather than a linked HTTP package.
