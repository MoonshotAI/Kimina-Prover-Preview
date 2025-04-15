import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1983_p2 (x p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15) (h₁ : p ≤ x ∧ x ≤ 15)
    (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : 15 ≤ f x := by
  have h3 : abs (x - p) = x - p := by
    rw [abs_of_nonneg]
    linarith [h₁.left]
  have h4 : abs (x - 15) = -(x - 15) := by
    rw [abs_of_nonpos]
    linarith [h₁.right]
  have h5 : abs (x - p - 15) = -(x - p - 15) := by
    rw [abs_of_nonpos]
    have h6 : x - p - 15 ≤ 0 := by linarith [h₁.right, h₀.left]
    linarith
  rw [h₂, h3, h4, h5]
  linarith [h₁.right]