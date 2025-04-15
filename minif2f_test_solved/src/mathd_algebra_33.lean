import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have hy : y = (2 / 5) * x := by
    linarith
  rw [hy] at h₂
  have hz : z = (7 / 25) * x := by
    linarith
  have h : z / x = 7 / 25 := by
    have h₅ : x ≠ 0 := h₀
    have h₆ : z = (7 / 25) * x := by linarith
    field_simp [h₅]
    linarith [h₆]
  exact h