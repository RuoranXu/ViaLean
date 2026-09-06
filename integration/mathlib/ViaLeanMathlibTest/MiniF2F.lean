import MiniF2F.ProblemImports
import ViaLeanMathlib.Benchmark

open BigOperators
open Lean Meta Elab Tactic ViaLean ViaLean.Mathlib

/-!
Smoke cases copied from the Google DeepMind Lean 4 miniF2F validation/test
statements at upstream revision `f0a20e1` (Lean/mathlib v4.27.0). The upstream
Lean statements are Apache-2.0 licensed; provenance and theorem names are
retained below.

Only `MiniF2F.ProblemImports` is imported. `MiniF2F.Valid` and `MiniF2F.Test`
are deliberately not imported, so their `sorry`-backed theorem constants
cannot enter premise retrieval and solve these cases by name. Each case emits
a `vialean.dataset.v1` JSON record before its proof is accepted.
-/

-- valid: mathd_numbertheory_132
example : 2004 % 12 = answer(0) := by
  vialean_dataset_case "miniF2F" "valid" "mathd_numbertheory_132"
    (timeoutSec := 10) (library := false)

-- valid: mathd_numbertheory_188
example : Nat.gcd 180 168 = answer(12) := by
  vialean_dataset_case "miniF2F" "valid" "mathd_numbertheory_188"
    (timeoutSec := 10) (library := false)

-- valid: mathd_algebra_182; exercises the ring leaf backend.
example (y : ℂ) : 7 * (3 * y + 2) = answer(21 * y + 14) := by
  vialean_dataset_case "miniF2F" "valid" "mathd_algebra_182"
    (timeoutSec := 10) (library := false)

-- valid: mathd_algebra_462; exercises rational normalization.
example : ((1 : ℚ) / 2 + 1 / 3) * (1 / 2 - 1 / 3) = answer(5 / 36) := by
  vialean_dataset_case "miniF2F" "valid" "mathd_algebra_462"
    (timeoutSec := 10) (library := false)

-- test: mathd_numbertheory_551
example : 1529 % 6 = answer(5) := by
  vialean_dataset_case "miniF2F" "test" "mathd_numbertheory_551"
    (timeoutSec := 10) (library := false)

-- test: mathd_algebra_44. ViaLean exposes the conjunction and the mathlib
-- leaf backend closes the resulting linear obligations after the default deep Atlas.
example (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) :
    And (s = 1) (t = 4) := by
  vialean_dataset_case "miniF2F" "test" "mathd_algebra_44"
    (timeoutSec := 15) (library := false)
