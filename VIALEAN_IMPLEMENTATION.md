# ViaLean implementation

## Scope

ViaLean is an independent Lean 4 proof-search library. Its leaf solver, symbolic frontier, bridge search, scheduling, validation, optional model guidance, tracing, and tactic frontend are implemented in this repository with ordinary Lean metaprogramming APIs.

The engine is deliberately bounded. It searches a small, semantically varied near frontier plus a shallow multi-step future graph instead of launching many long speculative rollouts.

## Search model

A node owns a goal, global deadline, depth, path fingerprints, discrete feedback storage, populated solve counters, and a guidance cache. The controller performs a cheap close, collects proof actions, and—only in interactive mode—constructs one diversity-balanced frontier atlas for all model rounds at that node. Retrieved library candidates retain their declaration names and replay by applying that exact theorem before recursively solving its generated obligations.

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

Interactive models are not limited to action selection. A response can contain complete or partial Lean tactic scripts. ViaLean parses them as `by` proofs/tactic sequences, rejects executable metaprogramming and non-core syntax, executes each accepted candidate on a fresh metavariable under a fresh heartbeat budget, then hands remaining goals to the ordinary model-disabled solver. Failure feedback includes parse/elaboration errors or open goals enriched with their own future paths.

The native solver independently supports exact hypotheses, reflexivity, `True`, contradiction, simplification/rewrite normalization, dependent introductions, constructors, bounded propositional cases, local/global premise application, and recursive subgoal solving.

## Bounds

- `frontierMaxProbes`: total atlas size.
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
- `ViaLean/Goal.lean`: goal snapshots and fingerprints.
- `ViaLean/Proposal.lean`, `Action.lean`: project-owned action representation.
- `ViaLean/Frontier.lean`: bounded multi-perspective previews, recursive future paths, and private replay handles.
- `ViaLean/NativeSolver.lean`: independent bounded leaf solver.
- `ViaLean/Model/Protocol.lean`: policy/interactive JSON, future views, Lean candidates, detailed feedback, and optional selection parsing.
- `ViaLean/Model/Process.lean`: shell-free process execution, streaming output bounds, and timeout termination.
- `ViaLean/Model/Provider.lean`: command, replay, and OpenAI-compatible transports.
- `ViaLean/Model/Guidance.lean`: bounded request rendering.
- `ViaLean/Search.lean`: AND/OR control, theorem/probe replay, safe model tactic execution, symbolic completion, feedback, deadline cancellation, and rollback.
- `ViaLean/Compose.lean`, `Validate.lean`: proof construction and trust boundary.
- `ViaLean/Tactic.lean`: `propose` and `propose?`.
- `ViaLeanTest/`: regression, frontier diversity, protocol, replay, and safety tests.

## Safety invariants

1. A returned proof contains no unresolved synthetic metavariables.
2. Every returned expression is checked against the requested target.
3. Preview and failed replay branches restore their metavariable state.
4. Search never accepts `sorry`/`admit`, unresolved holes, declarations, commands, native execution, or arbitrary model metaprograms.
5. Model tactic syntax is core-only and rejects `run_tac`, evaluation/native tactics, option overrides, macros, syntax quotations, and non-core extensions.
6. Every accepted model tactic runs on a fresh goal with a source-size bound, candidate-count bound, and fresh nonzero heartbeat cap.
7. Model-generated subgoals and selected replay disable nested model calls.
8. Observation-only probes and future paths cannot close a goal.
9. Provider failures, malformed code, and malformed selections degrade to ordinary search.
10. Provider calls, frontier expansion, and recursive solving share the global deadline.
11. The original goal is assigned only after complete candidate validation.

## Compatibility policy

The package has no Lake dependencies and no version-specific runtime linkage. It uses Lean's metaprogramming surface without release-number tests or per-version branches. Toolchain selection remains explicit for reproducible builds; API transport uses the external `curl` executable rather than a linked HTTP package.
