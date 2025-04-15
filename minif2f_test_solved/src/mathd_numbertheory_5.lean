import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
        rcases h₁ with ⟨x, hx⟩
        rcases h₂ with ⟨t, ht⟩
        by_contra h
        push_neg at h
        have h3 : n < 64 := by linarith
        have h4 : x < 8 := by nlinarith [hx, h3]
        have h5 : t < 4 := by
            have h6 : t ^ 3 < 64 := by linarith [ht, h3]
            by_contra h7
            push_neg at h7
            have h8 : t ^ 3 ≥ 64 := by
                have h9 : t ≥ 4 := by linarith
                have h10 : t ^ 3 ≥ 4 ^ 3 := by
                    exact Nat.pow_le_pow_of_le_left h9 3
                norm_num at h10
                linarith
            linarith [h6, h8]
        interval_cases t <;> interval_cases x <;> omega