import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by
  have h2 : 120 * b = 8 * 3720 := by
    calc
      120 * b = Nat.gcd 120 b * Nat.lcm 120 b := by rw [Nat.gcd_mul_lcm]
      _ = 8 * 3720 := by rw [h₁, h₀]
  have h3 : b = 248 := by
    linarith
  exact h3