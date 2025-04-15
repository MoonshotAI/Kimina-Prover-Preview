import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2020_p22 (t : ℝ) : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by

  have h1 : (2:ℝ) ^ (2 * t) - 12 * (2:ℝ) ^ t * t + 36 * t ^ 2 ≥ 0 := by
    have h2 : (2:ℝ) ^ (2 * t) - 12 * (2:ℝ) ^ t * t + 36 * t ^ 2 = (2 ^ t - 6 * t) ^ 2 := by
      ring_nf
      <;> simp [Real.rpow_mul, Real.rpow_add]
      <;> ring
    rw [h2]
    apply sq_nonneg

  have h3 : (4:ℝ) ^ t > 0 := by
    apply Real.rpow_pos_of_pos
    norm_num

  have h4 : (2 ^ t - 3 * t) * t ≤ (1 / 12) * (4 ^ t) := by
    have h4 : (4:ℝ) ^ t = (2:ℝ) ^ (2 * t) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
      rw [Real.rpow_mul]
      all_goals linarith
    nlinarith [h1, h4, Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]

  have h5 : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by
    have h_pos : (4:ℝ) ^ t > 0 := by
      apply Real.rpow_pos_of_pos
      norm_num
    apply (div_le_iff₀ h_pos).mpr
    linarith [h4]

  linarith [h5]