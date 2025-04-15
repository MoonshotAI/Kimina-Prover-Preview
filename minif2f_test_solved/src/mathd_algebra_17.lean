import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) : a = 8 := by
  have h1 : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
    have h16 : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
      have h16_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
      have h1 : Real.sqrt (16 + 16 * a) = Real.sqrt (4^2 * (1 + a)) := by
        have h2 : 16 + 16 * a = (4 : ℝ) ^ 2 * (1 + a) := by ring
        rw [h2]
      rw [h1]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
    have h2 : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = Real.sqrt (4 + 4 * Real.sqrt (1 + a)) := by
      rw [h16]
    rw [h2]
    have h3 : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
      have h3_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
      have h4_nonneg : 0 ≤ Real.sqrt (1 + Real.sqrt (1 + a)) := Real.sqrt_nonneg (1 + Real.sqrt (1 + a))
      have h4 : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
        have h5 : (Real.sqrt (4 + 4 * Real.sqrt (1 + a))) ^ 2 = (2 * Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 := by
          have h5_left : (Real.sqrt (4 + 4 * Real.sqrt (1 + a))) ^ 2 = 4 + 4 * Real.sqrt (1 + a) := by
            rw [Real.sq_sqrt]
            nlinarith [Real.sqrt_nonneg (1 + a), Real.sqrt_nonneg (1 + Real.sqrt (1 + a))]
          have h5_right : (2 * Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 4 + 4 * Real.sqrt (1 + a) := by
            calc
              (2 * Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2
                  = 2^2 * (Real.sqrt (1 + Real.sqrt (1 + a)))^2 := by ring
              _ = 4 * (1 + Real.sqrt (1 + a)) := by
                have h6 : (Real.sqrt (1 + Real.sqrt (1 + a)))^2 = 1 + Real.sqrt (1 + a) := by
                  rw [Real.sq_sqrt]
                  linarith [Real.sqrt_nonneg (1 + a), Real.sqrt_nonneg (1 + Real.sqrt (1 + a))]
                rw [h6]
                all_goals linarith
              _ = 4 + 4 * Real.sqrt (1 + a) := by ring
          rw [h5_left, h5_right]
        have h6 : 0 ≤ Real.sqrt (4 + 4 * Real.sqrt (1 + a)) := Real.sqrt_nonneg (4 + 4 * Real.sqrt (1 + a))
        have h7 : 0 ≤ 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
          apply mul_nonneg
          norm_num
          exact Real.sqrt_nonneg (1 + Real.sqrt (1 + a))
        have h8 : Real.sqrt (4 + 4 * Real.sqrt (1 + a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
          apply (sq_eq_sq h6 h7).mp
          linarith
        exact h8
      exact h4
    linarith [h3]
  rw [h1] at h₀
  have h2 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := by
    have h2_pos : 0 ≤ Real.sqrt (1 + Real.sqrt (1 + a)) := Real.sqrt_nonneg (1 + Real.sqrt (1 + a))
    nlinarith [Real.sqrt_nonneg (1 + Real.sqrt (1 + a)), h₀]
  have h3 : 1 + Real.sqrt (1 + a) = 4 := by
    have h3_pos : 0 ≤ Real.sqrt (1 + Real.sqrt (1 + a)) := Real.sqrt_nonneg (1 + Real.sqrt (1 + a))
    have h3_eq : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = (2 : ℝ) ^ 2 := by
      rw [h2]
    have h3_left : (Real.sqrt (1 + Real.sqrt (1 + a))) ^ 2 = 1 + Real.sqrt (1 + a) := by
      rw [Real.sq_sqrt]
      have h4 : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
      linarith [h4, Real.sqrt_nonneg (1 + Real.sqrt (1 + a))]
    have h3_right : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [h3_left, h3_right] at h3_eq
    linarith
  have h4 : Real.sqrt (1 + a) = 3 := by linarith [h3]
  have h5 : 1 + a = 9 := by
    have h5_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg (1 + a)
    have h5_eq : (Real.sqrt (1 + a)) ^ 2 = (3 : ℝ) ^ 2 := by
      rw [h4]
    have h5_left : (Real.sqrt (1 + a)) ^ 2 = 1 + a := by
      rw [Real.sq_sqrt]
      have h4_pos : 0 ≤ 1 + a := by
        by_contra h
        push_neg at h
        have h5 : Real.sqrt (1 + a) = 0 := by
          apply Real.sqrt_eq_zero_of_nonpos
          linarith
        rw [h5] at h4
        linarith
      exact h4_pos
    have h5_right : (3 : ℝ) ^ 2 = 9 := by norm_num
    rw [h5_left, h5_right] at h5_eq
    linarith
  linarith [h5]