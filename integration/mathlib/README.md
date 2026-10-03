# ViaLean mathlib integration

This isolated Lake project keeps the ViaLean core dependency-free while
compiling the same search engine inside a pinned mathlib environment.

The adapter pins mathlib `v4.27.0` and supplies:

- `mathlibLeafSolver`, a bounded portfolio of reviewed mathlib tactics;
- `mathlibRouter`, which combines those leaves with ViaLean's native fallback;
- `propose_mathlib`, the ordinary Atlas/search tactic using that router; and
- the reviewed syntax boundary for optional model-generated mathlib tactics.

Build the adapter with:

```console
cd integration/mathlib
lake update
lake exe cache get
lake build
```

The root package remains dependency-free. Model proposals and mathlib tactic
results are accepted only after ViaLean finalizes an ordinary Lean proof term
and the kernel checks it.
