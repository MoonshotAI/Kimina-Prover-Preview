import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have ha : a = Real.logb 4 5 := by
    rw [←h₁]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  have hb : b = Real.logb 5 6 := by
    rw [←h₂]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  have hc : c = Real.logb 6 7 := by
    rw [←h₃]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  have hd : d = Real.logb 7 8 := by
    rw [←h₄]
    field_simp [Real.logb_eq_iff_rpow_eq]
    all_goals linarith
  have h : a * b * c * d = Real.logb 4 5 * Real.logb 5 6 * Real.logb 6 7 * Real.logb 7 8 := by
    rw [ha, hb, hc, hd]
  rw [h]
  have h1 : Real.logb 4 5 * Real.logb 5 6 * Real.logb 6 7 * Real.logb 7 8 = 3 / 2 := by
    have h1 : Real.logb 4 5 = Real.log 5 / Real.log 4 := by
      field_simp [Real.logb]
    have h2 : Real.logb 5 6 = Real.log 6 / Real.log 5 := by
      field_simp [Real.logb]
    have h3 : Real.logb 6 7 = Real.log 7 / Real.log 6 := by
      field_simp [Real.logb]
    have h4 : Real.logb 7 8 = Real.log 8 / Real.log 7 := by
      field_simp [Real.logb]
    rw [h1, h2, h3, h4]
    have h5 : Real.log 8 = 3 * Real.log 2 := by
      calc
        Real.log 8 = Real.log (2 ^ 3) := by norm_num
        _ = 3 * Real.log 2 := by simp [Real.log_pow]
    have h6 : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]
    have h7 : Real.log 2 ≠ 0 := by
      have h_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    field_simp [h5, h6]
    <;> linarith [h7]
  linarith [h1]