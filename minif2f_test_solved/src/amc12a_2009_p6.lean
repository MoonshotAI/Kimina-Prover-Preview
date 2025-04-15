import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2009_p6 (m n p q : ℝ) (h₀ : p = 2 ^ m) (h₁ : q = 3 ^ n) :
    p ^ (2 * n) * q ^ m = 12 ^ (m * n) := by
  rw [h₀, h₁]
  have h2 : (2 : ℝ) ^ (m * (2 * n)) * (3 : ℝ) ^ (n * m) = (12 : ℝ) ^ (m * n) := by
    have h3 : (12 : ℝ) = 2 ^ (2 : ℝ) * 3 ^ (1 : ℝ) := by norm_num
    rw [h3]
    have h4 : (2 ^ (2 : ℝ) * 3 ^ (1 : ℝ)) ^ (m * n) = (2 : ℝ) ^ (2 * (m * n)) * (3 : ℝ) ^ (1 * (m * n)) := by
      rw [Real.mul_rpow (by norm_num) (by norm_num)]
      simp [Real.rpow_mul]
      all_goals linarith
    rw [h4]
    ring_nf
  rw [←h2]
  <;> simp [Real.rpow_mul]
  all_goals linarith