import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by 
  have h2 : (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
  have h3 : (1 / 2 : ℝ) - a⁻¹ = 1 := by 
    rw [h2] at h₁ 
    exact h₁
  have h4 : a⁻¹ = -1 / 2 := by
    linarith
  have h5 : a = -2 := by 
    have h6 : a ≠ 0 := h₀
    have h7 : a = -2 := by
      field_simp [h6] at h4
      linarith
    exact h7
  exact h5