import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have ht : t = 4 := by 
    linarith [h₀, h₁]
  have hs : s = 1 := by
    linarith [h₀, ht]
  exact ⟨hs, ht⟩