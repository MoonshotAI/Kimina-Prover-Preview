import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h4 : m = n + 2 := by
    omega
  rw [h4] at h₃
  have h5 : n ≤ 17 := by
    nlinarith
  interval_cases n <;> omega