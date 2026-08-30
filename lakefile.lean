import Lake

open Lake DSL

package ViaLean where
  version := v!"0.4.1"

@[default_target]
lean_lib ViaLean where
  roots := #[`ViaLean]

@[test_driver]
lean_lib ViaLeanTest where
  roots := #[`ViaLeanTest]
