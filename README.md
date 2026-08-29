# ViaLean

ViaLean is a small, kernel-checked proof-search engine implemented entirely in Lean 4. It combines bounded native proof search with explicit bridge actions.

## Design

The implementation has no external theorem-prover dependency, native extension, FFI, network service, or generated-code trust boundary. Search runs in `MetaM`, builds ordinary Lean expressions, and validates every candidate against the requested target before assigning the original goal. Lean's kernel remains the final authority.

The search pipeline is organized around project-owned data structures:

1. `GoalSnapshot` captures the target and local context.
2. proposal providers produce deterministic bridge candidates.
3. `ProofAction` represents direct closure, structural decomposition, equality or equivalence bridges, cuts, and witnesses.
4. the native leaf solver performs bounded introduction, constructor, local-hypothesis, and premise application.
5. the controller composes successful child proofs and validates the result.

Failed branches restore the metavariable context. A global deadline, depth limits, application limits, fingerprints, deterministic ordering, and optional UCB scheduling keep search bounded and reproducible.

## Tactics

`propose` searches for and closes the current goal. `propose?` runs diagnostics without closing it. Explicit bridge syntax is available when the intended intermediate object is known:

```lean
propose via_eq term
propose via_iff proposition
propose via_cut proposition
propose via_witness term
```

Common configuration fields include `timeoutSec`, `directProbeSec`, `candidateProbeSec`, `maxDepth`, `nativeMaxDepth`, `nativeMaxApplications`, `structural`, `cuts`, `equalityBridge`, `iffBridge`, `witnesses`, `library`, `ucb`, `deterministic`, and `trace`.

## Build and test

```console
lake build
lake test
```

The repository contains no package dependency, so builds need only the Lean toolchain selected by `lean-toolchain`. The implementation does not inspect a Lean version string or branch on a release number. When Lean changes a metaprogramming API, compatibility edits stay localized in the native solver and tactic frontend rather than leaking into the search model.

See [VIALEAN_IMPLEMENTATION.md](VIALEAN_IMPLEMENTATION.md) for the module map and safety invariants.

## License

MIT
