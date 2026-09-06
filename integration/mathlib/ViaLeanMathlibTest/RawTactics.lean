import Mathlib.Data.Real.Basic
import ViaLeanMathlib

example : (7 : ℝ) < 11 := by norm_num

example (s t : ℝ) (h0 : s = 9 - 2 * t) (h1 : t = 3 * s + 1) :
    And (s = 1) (t = 4) := by
  constructor <;> linarith
