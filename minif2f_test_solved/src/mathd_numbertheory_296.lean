import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_296 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : ∃ x, x ^ 3 = n) (h₂ : ∃ t, t ^ 4 = n) :
    4096 ≤ n := by 
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨t, ht⟩
  by_contra h
  push_neg at h
  have h3 : n < 4096 := h
  have h4 : x ^ 3 = t ^ 4 := by linarith
  have h5 : x ≤ 15 := by
    have h6 : x ^ 3 < 4096 := by linarith
    by_contra h7
    push_neg at h7
    have h8 : x ^ 3 ≥ 4096 := by
      have h9 : x ≥ 16 := by linarith
      have h10 : x ^ 3 ≥ 16 ^ 3 := by
        apply Nat.pow_le_pow_of_le_left h9 3
      norm_num at h10
      linarith
    linarith
  have h6 : t ≤ 7 := by
    have h7 : t ^ 4 < 4096 := by linarith
    by_contra h8
    push_neg at h8
    have h9 : t ≥ 8 := by linarith
    have h10 : t ^ 4 ≥ 4096 := by
      have h11 : t ^ 4 ≥ 8 ^ 4 := by
        apply Nat.pow_le_pow_of_le_left h9 4
      norm_num at h11
      linarith
    linarith
  interval_cases x <;> interval_cases t <;> omega