import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = 1 / 3 := by
    rw [h₀ 1 (by norm_num)]
    norm_num
  have h2 : f (1 / 3) = 3 / 7 := by 
    rw [h₀ (1 / 3) (by norm_num)]
    norm_num
  rw [h1]
  exact h2