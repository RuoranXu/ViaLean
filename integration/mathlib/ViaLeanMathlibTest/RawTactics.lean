import Mathlib.Data.Real.Basic
import ViaLeanMathlib

example : (7 : ℝ) < 11 := by norm_num

example (s t : ℝ) (h0 : s = 9 - 2 * t) (h1 : t = 3 * s + 1) :
    And (s = 1) (t = 4) := by
  constructor <;> linarith

example (s t : ℝ) (h0 : s = 9 - 2 * t) (h1 : t = 3 * s + 1) :
    And (s = 1) (t = 4) := by
  propose_mathlib (timeoutSec := 15) (library := false)
-- Dense rational linear arithmetic after structural opening.
example (b h v : ℝ) (hpos : 0 < b ∧ 0 < h ∧ 0 < v)
    (hv : v = 1 / 3 * (b * h)) (hb : b = 30) (hh : h = 13 / 2) : v = 65 := by
  norm_num at *
  nlinarith
-- Closed telescope form used by dataset commands.
example : ∀ (b h v : ℝ), (0 < b ∧ 0 < h ∧ 0 < v) →
    v = 1 / 3 * (b * h) → b = 30 → h = 13 / 2 → v = 65 := by
  intros
  norm_num at *
  nlinarith
-- End-to-end generic closure through ViaLean.
example : ∀ (b h v : ℝ), (0 < b ∧ 0 < h ∧ 0 < v) →
    v = 1 / 3 * (b * h) → b = 30 → h = 13 / 2 → v = 65 := by
  propose_mathlib (timeoutSec := 15) (library := false)
-- Kernel-checked composition of generic quadratic helper facts around a norm.
example (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  propose_mathlib (timeoutSec := 30) (library := false)
-- The same search from a closed telescope also exercises structural opening.
example : ∀ (a b : ℝ), a ^ 2 + b ^ 2 = 1 →
    a * b + ‖a - b‖ ≤ 1 := by
  propose_mathlib (timeoutSec := 30) (library := false)
-- Equality propagation through both directions of a local equivalence is a
-- symbolic transformation, independent of arithmetic and concrete carriers.
example {α : Type} (σ : α ≃ α) (a b c : α)
    (h0 : σ.symm a = b) (h2 : σ.symm c = a) :
    σ (σ b) = c := by
  propose_mathlib (timeoutSec := 15) (library := false)
