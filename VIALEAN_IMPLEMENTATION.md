# ViaLean implementation

## Scope

ViaLean is an independent Lean 4 proof-search library. Its leaf solver, symbolic frontier, bridge search, scheduling, validation, optional model guidance, tracing, and tactic frontend are implemented in this repository with ordinary Lean metaprogramming APIs.

The engine is deliberately bounded. It searches a small, semantically varied near frontier instead of launching many long speculative rollouts.

## Search model

A node owns a goal, global deadline, depth, path fingerprints, discrete feedback storage, and a guidance cache. The controller performs a cheap close, collects proof actions, and—only in interactive mode—constructs one diversity-balanced frontier atlas for all model rounds at that node.

The atlas separates symbolic perspectives so one prolific family cannot dominate:

- weak-head, target-star, and context normalization;
- local contradiction closure;
- each equality in both rewrite orientations;
- one-layer elimination of bounded inductive propositions;
- each target constructor and its coupled obligations;
- backward application of local declarations;
- typed local forward closure up to `frontierForwardDepth`;
- kernel-typed two-edge equality transitivity.

Preview tactics run under saved metavariable states and retain rendered strings only. Executable probes also retain private stable replay handles (`FVarId` or constructor name), which are never serialized. When selected, the controller creates a fresh goal, replays exactly that operation, disables nested model queries, recursively solves the generated metavariables, and extracts the completed root assignment. Failure restores the complete branch while IO feedback remains available for the next model round.

The native solver independently supports exact hypotheses, reflexivity, `True`, contradiction, simplification/rewrite normalization, dependent introductions, constructors, bounded propositional cases, local/global premise application, and recursive subgoal solving.

## Bounds

- `frontierMaxProbes`: total atlas size.
- `frontierMaxPerPerspective`: quota before round-robin merging.
- `frontierMaxChildren`: maximum displayed or replayed branch fan-out.
- `frontierMaxFacts`: maximum forward/equality facts.
- `frontierForwardDepth`: typed forward-composition depth.
- `frontierContextChars`: rendering budget for atlas items.
- `modelMaxRounds` and `modelMaxFeedbackEvents`: interaction bounds.
- `nativeMaxDepth`, `nativeMaxApplications`, and the shared deadline: recursive execution bounds.

## Modules

- `ViaLean/Config.lean`: search, frontier, and provider configuration.
- `ViaLean/Goal.lean`: goal snapshots and fingerprints.
- `ViaLean/Proposal.lean`, `Action.lean`: project-owned action representation.
- `ViaLean/Frontier.lean`: bounded multi-perspective previews and private replay handles.
- `ViaLean/NativeSolver.lean`: independent bounded leaf solver.
- `ViaLean/Model/Protocol.lean`: policy/interactive JSON, frontier views, and selection parsing.
- `ViaLean/Model/Process.lean`: shell-free process execution and timeout termination.
- `ViaLean/Model/Provider.lean`: command, replay, and OpenAI-compatible transports.
- `ViaLean/Model/Guidance.lean`: bounded request rendering.
- `ViaLean/Search.lean`: AND/OR control, probe replay, model isolation, feedback, and rollback.
- `ViaLean/Compose.lean`, `Validate.lean`: proof construction and trust boundary.
- `ViaLean/Tactic.lean`: `propose` and `propose?`.
- `ViaLeanTest/`: regression, frontier diversity, protocol, replay, and safety tests.

## Safety invariants

1. A returned proof contains no unresolved synthetic metavariables.
2. Every returned expression is checked against the requested target.
3. Preview and failed replay branches restore their metavariable state.
4. Search never uses `sorry`, `admit`, `unsafe`, generated proof text, or native code loading.
5. A model can select only serialized existing actions or executable probes; private replay handles are created by ViaLean.
6. Model-selected replay disables nested model calls.
7. Observation-only probes cannot close a goal.
8. Provider failures and malformed selections degrade to native search.
9. Provider calls and recursive solving share the global deadline.
10. The original goal is assigned only after complete candidate validation.

## Compatibility policy

The package has no Lake dependencies and no version-specific runtime linkage. It uses Lean's metaprogramming surface without release-number tests or per-version branches. Toolchain selection remains explicit for reproducible builds; API transport uses the external `curl` executable rather than a linked HTTP package.