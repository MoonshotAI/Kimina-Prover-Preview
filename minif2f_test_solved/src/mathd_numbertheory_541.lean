import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by
  have h3 : m ≤ 2005 := by nlinarith
  have h4 : n ≤ 2005 := by nlinarith
  interval_cases m <;> omega