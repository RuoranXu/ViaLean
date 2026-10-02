# Third-party notices

## miniF2F

`integration/mathlib/ViaLeanMathlibTest/MiniF2FTestDataset.lean` mechanically
adapts the first 24 theorem statements from the pinned Google DeepMind Lean 4
miniF2F test split. It omits all proof bodies and does not import the module
that declares the upstream target theorems.

Copyright (c) 2021 OpenAI. All rights reserved.

Authors: Kunhao Zheng, Kudzo Ahegbebu, Stanislas Polu, David Renshaw,
OpenAI GPT-f.

The adapted statements are distributed under the Apache License 2.0. The
license text is available at [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt).
The pinned upstream revision is recorded in
`integration/mathlib/lake-manifest.json`.
