# ViaLean implementation

## Scope

ViaLean is an independent Lean 4 proof-search library. Its leaf solver, bridge search, scheduling, validation, optional model guidance, tracing, and tactic frontend are implemented in this repository with ordinary Lean metaprogramming APIs.

The engine is deliberately bounded. It is intended to find short compositional proofs, not to replace domain-specific automation.

## Search model

A search node owns a goal, remaining budget, depth, path fingerprints, and a shared guidance cache. The controller first tries a cheap native close, then constructs every enabled proof action. When model guidance is enabled, an untrusted provider returns a node value and scores for those existing action IDs. ViaLean mixes the scores with local priors, tries each action under a saved metavariable state, and restores failed branches.

The native solver supports:

- exact local hypotheses;
- reflexive equality and `True`;
- dependent introductions;
- inductive constructors;
- application of local declarations;
- application of explicitly supplied global premises;
- recursive solving of all generated subgoals.

`nativeMaxDepth` and `nativeMaxApplications` bound recursive expansion. The controller's deadline is passed to every leaf and model attempt, so nested search cannot silently acquire a fresh unbounded timeout.

## Modules

- `ViaLean/Config.lean`: public search and provider configuration.
- `ViaLean/Goal.lean`: stable goal snapshots and fingerprints.
- `ViaLean/Proposal.lean`: proposal protocol and deterministic ranking.
- `ViaLean/Action.lean`: project-owned proof-action representation.
- `ViaLean/NativeSolver.lean`: independent bounded leaf solver.
- `ViaLean/Model/Protocol.lean`: stable JSON request/response types and score validation.
- `ViaLean/Model/Process.lean`: shell-free process execution with termination on timeout.
- `ViaLean/Model/Provider.lean`: command, replay, and OpenAI-compatible transports.
- `ViaLean/Model/Guidance.lean`: bounded request rendering for each search node.
- `ViaLean/Search.lean`: AND/OR controller, guidance cache, score mixing, and rollback boundaries.
- `ViaLean/Compose.lean`: proof construction for successful actions.
- `ViaLean/Validate.lean`: target checking and metavariable rejection.
- `ViaLean/Tactic.lean`: `propose` and `propose?` syntax.
- `ViaLeanTest/`: executable regression, protocol, and safety tests.

## Safety invariants

1. A proof containing synthetic metavariables is never returned.
2. A returned expression is checked against the requested target.
3. Failed branches cannot retain assignments in the caller's metavariable context.
4. Search never uses `sorry`, `admit`, `unsafe`, native code loading, or generated proof text.
5. A model can score only action IDs already built by ViaLean; it cannot create an executable action.
6. Provider failures and malformed output degrade to native search.
7. Provider processes have a per-call timeout capped by the global deadline.
8. The original goal is assigned only after the complete candidate proof validates.

## Compatibility policy

The package has no Lake dependencies and no version-specific runtime linkage. Source compatibility is maintained against Lean's public metaprogramming surface. API mode uses the external `curl` executable rather than adding a linked HTTP package. Toolchain selection remains explicit for reproducible builds, while the implementation itself contains no release-number tests or per-version code paths.