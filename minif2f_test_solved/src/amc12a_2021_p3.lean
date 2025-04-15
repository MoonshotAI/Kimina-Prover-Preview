import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
  have h3 : x = 10 * y := by 
    have h4 : x = 10 * (x / 10) := by 
      omega
    rw [h4]
    rw [h₂]
  have hy : y = 1582 := by
    have h4 : 11 * y = 17402 := by 
      omega
    omega
  have hx : x = 15820 := by
    omega
  rw [hx, hy]
  norm_num