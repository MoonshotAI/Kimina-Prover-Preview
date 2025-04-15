import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h2 : x + 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h3 : x - 9 = 2 * (x + 1) := by
    field_simp [h2] at h₁
    linarith
  linarith