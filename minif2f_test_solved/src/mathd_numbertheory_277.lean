import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_277 (m n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126) :
    60 ≤ m + n := by 
  have h2 : m * n = 6 * 126 := by 
    calc
      m * n = Nat.gcd m n * Nat.lcm m n := by rw [Nat.gcd_mul_lcm]
      _ = 6 * 126 := by rw [h₀, h₁]
  by_contra h
  push_neg at h
  have h3 : m ≤ 60 := by nlinarith
  have h4 : n ≤ 60 := by nlinarith
  interval_cases m <;> interval_cases n <;> norm_num at h₀ h₁ h2 <;> all_goals 
    omega