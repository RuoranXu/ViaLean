# ViaLean implementation

## Scope

ViaLean is an independent Lean 4 proof-search library. Its leaf solver, bridge search, scheduling, validation, tracing, and tactic frontend are implemented in this repository with ordinary Lean metaprogramming APIs.

The engine is deliberately bounded. It is intended to find short compositional proofs, not to replace domain-specific automation.

## Search model

A search node owns a goal, remaining budget, depth, and path fingerprints. The controller first tries a native close, then enumerates enabled action families. Every action is tried under a saved metavariable state. Success commits a checked proof; failure restores the state before the next action.

The native solver supports:

- exact local hypotheses;
- reflexive equality and `True`;
- dependent introductions;
- inductive constructors;
- application of local declarations;
- application of explicitly supplied global premises;
- recursive solving of all generated subgoals.

`nativeMaxDepth` and `nativeMaxApplications` bound recursive expansion. The controller's deadline is passed to every leaf attempt, so nested search cannot silently acquire a fresh unbounded timeout.

## Modules

- `ViaLean/Config.lean`: public configuration and limits.
- `ViaLean/Goal.lean`: stable goal snapshots and fingerprints.
- `ViaLean/Proposal.lean`: proposal protocol and deterministic ranking.
- `ViaLean/Action.lean`: project-owned proof-action representation.
- `ViaLean/NativeSolver.lean`: independent bounded leaf solver.
- `ViaLean/Search.lean`: AND/OR controller and rollback boundaries.
- `ViaLean/Compose.lean`: proof construction for successful actions.
- `ViaLean/Validate.lean`: target checking and metavariable rejection.
- `ViaLean/Tactic.lean`: `propose` and `propose?` syntax.
- `ViaLeanTest/`: executable regression and safety tests.

## Safety invariants

1. A proof containing synthetic metavariables is never returned.
2. A returned expression is checked against the requested target.
3. Failed branches cannot retain assignments in the caller's metavariable context.
4. Search never uses `sorry`, `admit`, `unsafe`, native code loading, or network execution.
5. The original goal is assigned only after the complete candidate proof validates.

## Compatibility policy

The package has no Lake dependencies and no version-specific runtime linkage. Source compatibility is maintained against Lean's public metaprogramming surface. Toolchain selection remains explicit for reproducible builds, while the implementation itself contains no release-number tests or per-version code paths.