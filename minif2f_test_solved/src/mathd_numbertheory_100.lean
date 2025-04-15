import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by 
  have h3 : n.gcd 40 * n.lcm 40 = n * 40 := by
    rw [Nat.gcd_mul_lcm]
  rw [h₁, h₂] at h3
  have h4 : n = 70 := by
    linarith
  exact h4