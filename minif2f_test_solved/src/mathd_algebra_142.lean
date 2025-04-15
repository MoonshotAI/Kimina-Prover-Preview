import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  have eq1 : m = -1 := by 
    linarith 
  have eq2 : b = 6 := by 
    rw [eq1] at h₀ 
    linarith
  linarith [eq1, eq2]