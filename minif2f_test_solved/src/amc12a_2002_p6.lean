import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by 
  use n + 1
  constructor
  . -- Show m > n
    omega
  . -- Find p such that (n + 1) * p ≤ (n + 1) + p
    use 1
    omega