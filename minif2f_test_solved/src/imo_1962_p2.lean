import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem imo_1962_p2 (x : ℝ) (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) : -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by 
  constructor
  · linarith [h₁]
  · have h3 : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 2 := by linarith
    have h4 : Real.sqrt (3 - x) > Real.sqrt (x + 1) + 1 / 2 := by linarith
    have h5 : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
    have h6 : Real.sqrt (3 - x) ≥ 0 := Real.sqrt_nonneg (3 - x)
    have h7 : Real.sqrt (3 - x) > 0 := by linarith [h6, h5]
    have h8 : (Real.sqrt (3 - x)) ^ 2 > (Real.sqrt (x + 1) + 1 / 2) ^ 2 := by
      apply sq_lt_sq'
      all_goals linarith [h4, h5, h7]
    have h9 : (Real.sqrt (3 - x)) ^ 2 = 3 - x := by 
      rw [Real.sq_sqrt]
      linarith
    have h10 : (Real.sqrt (x + 1) + 1 / 2) ^ 2 = (Real.sqrt (x + 1)) ^ 2 + Real.sqrt (x + 1) + 1 / 4 := by
      ring_nf
      <;> simp [Real.sqrt_nonneg]
    rw [h9, h10] at h8
    have h11 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h12 : Real.sqrt (x + 1) < 7 / 4 - 2 * x := by nlinarith [h8, h11, Real.sqrt_nonneg (x + 1)]
    have h13 : x < 1 - Real.sqrt 31 / 8 := by
      have h14 : Real.sqrt (x + 1) + 2 * x < 7 / 4 := by linarith [h12]
      have h15 : Real.sqrt 31 ^ 2 = 31 := by
        rw [Real.sq_sqrt]
        norm_num
      nlinarith [h14, Real.sq_sqrt (show 0 ≤ x + 1 by linarith), Real.sq_sqrt (show 0 ≤ 3 - x by linarith), Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show 0 ≤ (31 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (8 : ℝ) by norm_num)]
    linarith [h13]