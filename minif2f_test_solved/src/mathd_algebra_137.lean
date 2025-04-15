import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by 
  have h1 : (x : ℝ) + (4 : ℝ) / (100 : ℝ) * (x : ℝ) = 598 := by 
    exact_mod_cast h₀
  have hx : (x : ℝ) = 575 := by 
    linarith
  exact_mod_cast hx