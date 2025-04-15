import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_329 (x y : ℝ) (h₀ : 3 * y = x) (h₁ : 2 * x + 5 * y = 11) : x + y = 4 := by
  have hx : x = 3 * y := by linarith
  rw [hx] at h₁
  have hy : y = 1 := by
    linarith
  have hx2 : x = 3 := by
    rw [hy] at hx
    linarith
  linarith [hx2, hy]