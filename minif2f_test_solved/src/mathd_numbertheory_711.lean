import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_711 (m n : ℕ) (h₀ : 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 8)
    (h₂ : Nat.lcm m n = 112) : 72 ≤ m + n := by
  have h3 : m * n = 896 := by 
    calc
      m * n = m.gcd n * m.lcm n := by rw [Nat.gcd_mul_lcm]
      _ = 8 * 112 := by rw [h₁, h₂]
      _ = 896 := by norm_num
  by_contra h
  push_neg at h
  have h4 : m ≤ 71 := by nlinarith
  have h5 : n ≤ 71 := by nlinarith
  interval_cases m <;> interval_cases n <;> norm_num at h₁ h₂ h3 <;> omega