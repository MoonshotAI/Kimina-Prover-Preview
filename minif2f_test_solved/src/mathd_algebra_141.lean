import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  have h3 : a + b = 27 := by linarith
  have h4 : a^2 + b^2 = (a + b) ^ 2 - 2 * (a * b) := by 
    ring
  rw [h4, h3, h₁]
  norm_num