# Benchmark and corpus notes

ViaLean's in-repository evaluation is deliberately dependency-free. It is a
regression and ablation harness, not a claim of state-of-the-art performance on
an external benchmark.

## Matched-compute modes

ViaLean.Benchmark.matchedComputeModes runs eight modes with the same base
wall-clock, Atlas work, Meta-operation, and model-response limits:

1. native only;
2. symbolic actions only;
3. flat interactive frontier;
4. graph Atlas without a model;
5. Atlas plus policy;
6. Atlas plus policy/value and event-driven replan;
7. Atlas plus policy/value and a bounded expansion request;
8. opt-in interactive raw Lean baseline.

The replay provider makes neural decisions deterministic. Its first-region
placeholders are resolved from the real planner request, so the expansion mode
executes the normal region validation and allocation path.

Every vialean.benchmark.v3 JSON line records solve outcome, elapsed time,
direct/proposal attempts, bridge depth, model calls, replan count, Atlas
nodes/transitions, and Atlas Meta operations.

## Standard-library replay slice

ViaLeanTest/StdDataset.lean contains six targets adapted from declarations in
the active Lean toolchain:

- Nat.succ_ne_zero;
- List.append_nil;
- List.mem_cons_self;
- Array.reverse_reverse;
- BitVec.mul_zero;
- String.length_append.

The statements are re-declared as examples and solved by propose; their
original proofs are not referenced. This keeps the test useful across Lean
installations without adding mathlib or pinning an external dataset snapshot.

This six-case root slice is not miniF2F and must not be reported as a miniF2F
score.

## Lean 4 miniF2F / mathlib smoke suite

`integration/mathlib` pins the Google DeepMind Lean 4 miniF2F environment and
contains cases from both the validation and test splits. The copied goals import
only `MiniF2F.ProblemImports`; importing `MiniF2F.Valid` or `MiniF2F.Test` would
put the `sorry`-backed target theorem itself in the environment and invalidate
retrieval-based evaluation. Library retrieval is therefore also disabled for
those smoke cases. See `integration/mathlib/README.md` for reproduction steps.
