import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have ha : a = 5 := by
    have h2 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num [Real.rpow_natCast]
    have h3 : a = Real.logb 2 32 := by
      rw [←h₀]
      field_simp [Real.logb_eq_iff_rpow_eq]
      all_goals linarith
    rw [h3]
    have h4 : Real.logb 2 (32 : ℝ) = 5 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    linarith [h4]
  have hb : b = 3 := by
    rw [ha] at h₁
    have h5 : (5 : ℝ) ^ b = 125 := h₁
    have h6 : b = Real.logb 5 125 := by
      rw [←h5]
      field_simp [Real.logb_eq_iff_rpow_eq]
      all_goals linarith
    have h7 : Real.logb 5 (125 : ℝ) = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    rw [h6, h7]
  rw [ha, hb]
  norm_num [Real.rpow_natCast]