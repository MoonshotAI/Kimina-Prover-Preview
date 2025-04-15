import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h1 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + -3 + 5 := h₀ (-3)
  have h2 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := h₀ 3
  rw [h1] at h₂
  rw [h2]
  linarith [h₂]