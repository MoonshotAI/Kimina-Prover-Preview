import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by 
  by_contra h
  push_neg at h
  have h4 : k ≤ 4 := by linarith
  interval_cases k <;> try { 
    have h₁1 := h₁ 1
    have h₂1 := h₂ 1
    have h₃1 := h₃ 1
    norm_num at h₁1 h₂1 h₃1 
    all_goals omega
  }
  all_goals omega