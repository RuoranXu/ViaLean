import Lake

open Lake DSL

package ViaLeanMathlib where
  version := v!"0.1.0"

require ViaLean from "../.."
require minif2f from git
  "https://github.com/google-deepmind/miniF2F" @
  "f0a20e14c1eeccd859d51bb4c2b3ee487889c303"

@[default_target]
lean_lib ViaLeanMathlib where
  roots := #[`ViaLeanMathlib]

@[test_driver]
lean_lib ViaLeanMathlibTest where
  roots := #[`ViaLeanMathlibTest]
