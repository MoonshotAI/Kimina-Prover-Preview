import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by

  have h1 : Real.log 6 = Real.log 2 + Real.log 3 := by
    have h2 : Real.log 6 = Real.log (2 * 3) := by norm_num
    rw [h2]
    rw [Real.log_mul]
    all_goals linarith
  
  have h2 : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by
    rw [h1]
    field_simp [show Real.log 2 ≠ 0 by
      by_contra h
      have : Real.log 2 = 0 := by linarith
      have h3 : Real.log 2 > 0 := by
        apply Real.log_pos
        norm_num
      linarith
              , show Real.log 3 ≠ 0 by
        by_contra h
        have : Real.log 3 = 0 := by linarith
        have h3 : Real.log 3 > 0 := by
          apply Real.log_pos
          norm_num
        linarith]
    ring_nf
    <;> linarith [Real.log_pos (show (2 : ℝ) > 1 by norm_num), Real.log_pos (show (3 : ℝ) > 1 by norm_num)]

  rw [h2]
  
  have h3 : Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) ≥ 0 := by
    apply add_nonneg
    · apply Real.sqrt_nonneg
    · apply Real.sqrt_nonneg
  
  have h4 : Real.log 3 / Real.log 2 > 0 := by
    apply div_pos
    · have h3 : Real.log 3 > 0 := by
        apply Real.log_pos
        norm_num
      linarith
    · have h2 : Real.log 2 > 0 := by
        apply Real.log_pos
        norm_num
      linarith
  
  have h5 : Real.log 2 / Real.log 3 > 0 := by
    apply div_pos
    · have h2 : Real.log 2 > 0 := by
        apply Real.log_pos
        norm_num
      linarith
    · have h3 : Real.log 3 > 0 := by
        apply Real.log_pos
        norm_num
      linarith
  
  have h6 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  
    have h7 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) ≥ 0 := Real.sqrt_nonneg _
    
    have h8 : Real.sqrt (Real.log 3 / Real.log 2) ≥ 0 := Real.sqrt_nonneg _
  
    have h9 : Real.sqrt (Real.log 2 / Real.log 3) ≥ 0 := Real.sqrt_nonneg _
  
    have h10 : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by
      calc
        (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2
          = (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 + (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 + 2 * (Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3)) := by ring
        _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 * (Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3)) := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 * Real.sqrt ((Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3)) := by
          have h11 : Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) = Real.sqrt ((Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3)) := by
            rw [← Real.sqrt_mul (by positivity)]
          linarith [h11]
        _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 * Real.sqrt 1 := by
          have h12 : (Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3) = 1 := by
            field_simp [show Real.log 2 ≠ 0 by
              by_contra h
              have : Real.log 2 = 0 := by linarith
              have h3 : Real.log 2 > 0 := by
                apply Real.log_pos
                norm_num
              linarith
              , show Real.log 3 ≠ 0 by
                by_contra h
                have : Real.log 3 = 0 := by linarith
                have h3 : Real.log 3 > 0 := by
                  apply Real.log_pos
                  norm_num
                linarith]
          rw [h12]
        _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 * 1 := by
          rw [Real.sqrt_one]
        _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by ring
  
    have h11 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) ≥ 0 := Real.sqrt_nonneg _
  
    have h12 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
      have h13 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) ^ 2 = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
        rw [Real.sq_sqrt (by linarith [h4, h5]), h10]
      
      have h14 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) ≥ 0 := Real.sqrt_nonneg _

      have h15 : Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) ≥ 0 := by
        linarith [Real.sqrt_nonneg (Real.log 3 / Real.log 2), Real.sqrt_nonneg (Real.log 2 / Real.log 3)]

      have h16 : Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
        nlinarith [sq_nonneg (Real.sqrt (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) - (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3))), h13, Real.sqrt_nonneg (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2), Real.sqrt_nonneg (Real.log 3 / Real.log 2), Real.sqrt_nonneg (Real.log 2 / Real.log 3), h14, h15]
      exact h16
    exact h12
  exact h6