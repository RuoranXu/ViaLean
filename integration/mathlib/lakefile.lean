import Lake

open Lake DSL

package ViaLeanMathlib where
  version := v!"0.1.0"

require ViaLean from "../.."
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

@[default_target]
lean_lib ViaLeanMathlib where
  roots := #[`ViaLeanMathlib]
