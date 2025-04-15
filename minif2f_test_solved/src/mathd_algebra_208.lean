import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  have h1 : Real.sqrt 1000000 = 1000 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 100 := by
    have h21 : (1000000 : ℝ) = 100 ^ (3 : ℝ) := by norm_num
    rw [h21]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h1, h2]
  all_goals norm_num