import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_314 (r n : ℕ) (h₀ : r = 1342 % 13) (h₁ : 0 < n) (h₂ : 1342 ∣ n)
    (h₃ : n % 13 < r) : 6710 ≤ n := by
  have hr : r = 3 := by 
    norm_num [h₀]
  have h4 : r = 3 := hr

  rcases h₂ with ⟨k, hk⟩
  have h5 : n % 13 < 3 := by
    rw [h4] at h₃
    exact h₃

  rw [hk] at h5
  
  have h6 : k ≥ 5 := by
    by_contra h
    push_neg at h
    have h7 : k < 5 := h
    have h8 : k ≠ 0 := by
      omega
    interval_cases k <;> norm_num at h5 <;> omega

  have h9 : n = 1342 * k := by
    linarith

  have h10 : n ≥ 6710 := by
    omega

  linarith