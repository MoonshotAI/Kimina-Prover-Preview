import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have h1 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = (3 ^ (3 : ℝ)) by norm_num]
    simp [Real.log_rpow]
  have h2 : Real.log 3 ≠ 0 := by
    have h3 : Real.log 3 > 0 := by
      apply Real.log_pos
      norm_num
    linarith
  field_simp [h2]
  linarith [h1]