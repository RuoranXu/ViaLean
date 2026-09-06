# ViaLean mathlib / miniF2F integration

This isolated Lake project keeps the ViaLean core dependency-free while
compiling the same sources inside a real mathlib environment.

The dependency is pinned to Google DeepMind's Lean 4 miniF2F revision
`f0a20e14c1eeccd859d51bb4c2b3ee487889c303`, whose manifest pins
`formal_conjectures` and mathlib `v4.27.0` (mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`).

The integration supplies:

- `mathlibLeafSolver`: a bounded trusted portfolio of `norm_num`, `omega`,
  `linarith`, `ring_nf`, and `aesop`;
- `mathlibRouter`: mathlib leaves plus ViaLean's dependency-free native
  fallback;
- `propose_mathlib`: the ordinary Atlas/search engine using that router;
- `vialean_dataset_case`: a reusable tactic that emits one
  `vialean.dataset.v1` JSON record and accepts only a finalized proof;
- validation- and test-split miniF2F smoke cases with library retrieval
  disabled.

The smoke cases import only `MiniF2F.ProblemImports` and reproduce the upstream
statements. They do not import `MiniF2F.Valid` or `MiniF2F.Test`, because those
files declare the target theorems with `sorry`; importing them would let premise
retrieval select the answer itself.

Build with:

```console
cd integration/mathlib
lake update
lake exe cache get
lake test
```

To force a fresh elaboration and collect the six kernel-checked case records:

```console
lake env lean ViaLeanMathlibTest/MiniF2F.lean > minif2f-smoke.jsonl
```

Each output line is standalone JSON containing the dataset, split, theorem
name, solved flag, wall time, search attempts, model calls, replans, and Atlas
work. A failed proof writes its `solved: false` record and then fails the Lean
process, so benchmark data cannot silently report an unverified success.

The root `lake test` remains the fast zero-dependency suite. This integration
test is separate because mathlib's compiled cache is large and mathlib requires
its matching Lean toolchain.
