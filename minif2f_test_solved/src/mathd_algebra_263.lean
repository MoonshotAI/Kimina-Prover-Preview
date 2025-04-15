import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  have h2 : (Real.sqrt (19 + 3 * y)) ^ 2 = 49 := by
    rw [h₁]
    norm_num
  have h3 : (Real.sqrt (19 + 3 * y)) ^ 2 = 19 + 3 * y := by
    rw [Real.sq_sqrt h₀]
  rw [h3] at h2
  linarith