import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h3 : (x : ℤ) + (y : ℤ) = 36 := by
    have h2' : (x : ℤ) + (y : ℤ) = 36 := by
      omega
    exact h2'
  have h4 : (x : ℤ) = 6 := by
    have h1' : (y : ℤ) = 5 * (x : ℤ) := by 
      omega
    rw [h1'] at h3
    linarith 
  have hx : x = 6 := by
    norm_num at h4
    exact_mod_cast h4
  exact hx