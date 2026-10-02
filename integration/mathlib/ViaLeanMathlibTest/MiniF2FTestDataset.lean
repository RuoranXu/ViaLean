/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the upstream miniF2F LICENSE.
Authors: Kunhao Zheng, Kudzo Ahegbebu, Stanislas Polu, David Renshaw, OpenAI GPT-f

This file mechanically adapts the first 24 statements of the pinned
MiniF2F/Test.lean revision. Proof bodies are omitted, and targets are evaluated
without importing the module that declares the upstream theorems.
-/
import MiniF2F.ProblemImports
import ViaLeanMathlib.Benchmark

set_option maxRecDepth 1000
set_option linter.unusedVariables false
open scoped Real Nat Topology Polynomial
open ViaLean.Mathlib

#vialean_dataset_eval "miniF2F" "test" "mathd_algebra_478" (timeoutSec := 15) : ∀ (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2), v = 65

#vialean_dataset_eval "miniF2F" "test" "numbertheory_4x3m7y3neq2003" (timeoutSec := 15) : ∀ (x y : ℤ), 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003

#vialean_dataset_eval "miniF2F" "test" "aime_1983_p1" (timeoutSec := 15) : ∀ (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12), Real.log w / Real.log z = 60

#vialean_dataset_eval "miniF2F" "test" "amc12_2001_p5" (timeoutSec := 15) : Finset.prod (Finset.filter (fun x => ¬Even x) (Finset.range 10000)) (id : ℕ → ℕ) =
      10000! / (2 ^ 5000 * 5000!)

#vialean_dataset_eval "miniF2F" "test" "mathd_algebra_141" (timeoutSec := 15) : ∀ (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54), a ^ 2 + b ^ 2 = 369

#vialean_dataset_eval "miniF2F" "test" "mathd_numbertheory_3" (timeoutSec := 15) : (∑ x ∈ Finset.range 10, (x + 1) ^ 2) % 10 = 5

#vialean_dataset_eval "miniF2F" "test" "imo_1969_p2" (timeoutSec := 15) : ∀ (m n : ℝ) (k : ℕ) (a : ℕ → ℝ) (y : ℝ → ℝ) (h₀ : 0 < k)
    (h₁ : ∀ x, y x = ∑ i ∈ Finset.range k, Real.cos (a i + x) / 2 ^ i) (h₂ : y m = 0)
    (h₃ : y n = 0), ∃ t : ℤ, m - n = t * π

#vialean_dataset_eval "miniF2F" "test" "mathd_algebra_209" (timeoutSec := 15) : ∀ (σ : ℝ ≃ ℝ) (h₀ : σ.symm 2 = 10) (h₁ : σ.symm 10 = 1)
    (h₂ : σ.symm 1 = 2), σ (σ 10) = 1

#vialean_dataset_eval "miniF2F" "test" "mathd_numbertheory_1124" (timeoutSec := 15) : ∀ (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n), n = 4

#vialean_dataset_eval "miniF2F" "test" "imo_1983_p6" (timeoutSec := 15) : ∀ (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c), 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a)

#vialean_dataset_eval "miniF2F" "test" "mathd_numbertheory_237" (timeoutSec := 15) : (∑ k ∈ Finset.range 101, k) % 6 = 4

#vialean_dataset_eval "miniF2F" "test" "mathd_algebra_33" (timeoutSec := 15) : ∀ (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z), z / x = 7 / 25

#vialean_dataset_eval "miniF2F" "test" "amc12b_2021_p3" (timeoutSec := 15) : ∀ (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53), x = 3 / 4

#vialean_dataset_eval "miniF2F" "test" "mathd_numbertheory_299" (timeoutSec := 15) : 1 * 3 * 5 * 7 * 9 * 11 * 13 % 10 = 5

#vialean_dataset_eval "miniF2F" "test" "amc12b_2020_p2" (timeoutSec := 15) : (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1

#vialean_dataset_eval "miniF2F" "test" "algebra_sqineq_unitcircatbpabsamblt1" (timeoutSec := 15) : ∀ (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1), a * b + ‖a - b‖ ≤ 1

#vialean_dataset_eval "miniF2F" "test" "imo_1977_p6" (timeoutSec := 15) : ∀ (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)), ∀ n, 0 < n → f n = n

#vialean_dataset_eval "miniF2F" "test" "mathd_algebra_419" (timeoutSec := 15) : ∀ (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5), -a - b ^ 2 + 3 * (a * b) = -39

#vialean_dataset_eval "miniF2F" "test" "amc12a_2020_p10" (timeoutSec := 15) : ∀ (n : ℕ) (h₀ : 1 < n)
    (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)), (Nat.digits 10 n).sum = 13

#vialean_dataset_eval "miniF2F" "test" "imo_1960_p2" (timeoutSec := 15) : { x : ℝ |
      0 ≤ 1 + 2 * x ∧ (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0 ∧
      4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9 } = Set.Ico (-(1 / 2)) (45 / 8) \ {0}

#vialean_dataset_eval "miniF2F" "test" "mathd_numbertheory_427" (timeoutSec := 15) : ∀ (a : ℕ) (h₀ : a = ∑ k ∈ Nat.divisors 500, k), ∑ k ∈ Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k = 25

#vialean_dataset_eval "miniF2F" "test" "numbertheory_x5neqy2p4" (timeoutSec := 15) : ∀ (x y : ℤ), x ^ 5 ≠ y ^ 2 + 4

#vialean_dataset_eval "miniF2F" "test" "imoshortlist_2007_algebra_p6" (timeoutSec := 15) : ∀ (a : ℕ → NNReal)
    (h₀ : ∑ x ∈ Finset.range 100, a (x + 1) ^ 2 = 1), ∑ x ∈ Finset.range 99, a (x + 1) ^ 2 * a (x + 2) + a 100 ^ 2 * a 1 < 12 / 25

#vialean_dataset_eval "miniF2F" "test" "mathd_algebra_398" (timeoutSec := 15) : ∀ (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b), 63 * a = 80 * c
