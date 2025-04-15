import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h3 : a + b + c = 5 := by
    linarith
  have ha : a = -4 := by 
    linarith [h₀, h3]
  have hb : b = 2 := by 
    linarith [h₁, h3]
  have hc : c = 7 := by 
    linarith [h₂, h3] 
  rw [ha, hb, hc]
  norm_num