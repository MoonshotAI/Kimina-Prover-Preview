import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [h₀]
  have h1 : (16 * ((8 : ℝ) ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
    have h2 : (8 : ℝ) ^ 2 = (64 : ℝ) := by norm_num
    rw [h2]
    have h3 : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
      have h4 : (64 : ℝ) = 4 ^ (3 : ℝ) := by norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h4 : (16 : ℝ) * (64 : ℝ) ^ ((1 : ℝ) / 3) = (64 : ℝ) := by
      rw [h3]
      norm_num
    rw [h4]
    rw [h3]
  exact h1