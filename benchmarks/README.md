# Evaluation

ViaLean evaluates proof search with kernel-checked Lean terms, fixed resource
limits, and machine-readable JSONL records. The in-repository suite separates
dependency-free regression tests from the pinned mathlib/miniF2F integration.

## In-repository ablations

`ViaLean.Benchmark.matchedComputeModes` defines eight matched-compute modes:

1. native search;
2. symbolic actions;
3. an interactive flat frontier;
4. the model-free Proof Atlas;
5. Atlas search with policy guidance;
6. policy/value guidance with event-driven replanning;
7. bounded model-requested Atlas expansion; and
8. an opt-in raw-Lean baseline.

The modes share wall-clock, Atlas-work, Meta-operation, and model-response
limits. Deterministic replay providers make the model-guided paths suitable for
regression testing. Each `vialean.benchmark.v3` record includes the outcome,
latency, attempts, model calls, replans, Atlas size, and Meta-operation count.

Run the core suite from the repository root:

```console
lake test
```

## Standard-library regression slice

`ViaLeanTest/StdDataset.lean` re-declares six representative goals from the
active Lean toolchain and proves them without referring to their original
proofs. This is a portability and regression suite; it is not a miniF2F score.

## Mathlib and miniF2F

The separate project under `integration/mathlib` pins compatible Lean, mathlib,
and Google DeepMind Lean 4 miniF2F revisions. Dataset goals import only
`MiniF2F.ProblemImports`; target theorem modules are deliberately excluded, and
library retrieval is disabled for copied benchmark statements.

```console
cd integration/mathlib
lake update
lake exe cache get
lake test
```

For isolated, process-bounded cases, run the PowerShell harness through the
integration Lake environment:

```powershell
cd integration/mathlib
lake env powershell -File ../../benchmarks/run_minif2f_cases.ps1 `
  -Source ViaLeanMathlibTest/MiniF2FTestDataset.lean `
  -Output ../../benchmarks/results/minif2f-test.jsonl `
  -From 1 -To 24 -BudgetSec 15 -HardTimeoutSec 900
```

`-Resume` skips cases already present in the output. Each case runs in its own
Lean process, receives a cooperative search budget, and is also protected by a
process-level hard timeout. The hard limit includes Lean and mathlib startup, so
it must exceed the machine's cold-import latency; the 900-second default is a
ceiling, while `BudgetSec` remains the proof-search budget.

## Fixed evaluation slice

The repository includes one fixed-revision record:
[`results/minif2f-test-v0.6.0-001-024-15s.jsonl`](results/minif2f-test-v0.6.0-001-024-15s.jsonl).
It evaluates cases 1--24 of the miniF2F test split with the model-free
neural-ready symbolic configuration and a nominal 15-second search budget per
case.

| Split | Cases | Solved | Rate | Internal errors | Search exceptions |
|---|---:|---:|---:|---:|---:|
| miniF2F test | 24 | 11 | 45.8% | 0 | 5 |

This is a measured evaluation subset, not a full-split or state-of-the-art
claim. The JSONL file is the authoritative per-case record; accepted proofs are
elaborated and checked by Lean's kernel.
