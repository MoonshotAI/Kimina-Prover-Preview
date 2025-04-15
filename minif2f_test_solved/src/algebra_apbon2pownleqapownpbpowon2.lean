import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have h2 : a > 0 := h₀.left
  have h3 : b > 0 := h₀.right
  have h4 : n ≥ 1 := by linarith
  have base : ((a + b) / 2) ^ 1 ≤ (a ^ 1 + b ^ 1) / 2 := by
    linarith
  have step : ∀ k, k ≥ 1 → ((a + b) / 2) ^ k ≤ (a ^ k + b ^ k) / 2 → ((a + b) / 2) ^ (k + 1) ≤ (a ^ (k + 1) + b ^ (k + 1)) / 2 := by
    intro k hk h_k
    have h1 : ((a + b) / 2) ^ (k + 1) = ((a + b) / 2) ^ k * ((a + b) / 2) := by ring
    rw [h1]
    have h2 : ((a + b) / 2) ^ k * ((a + b) / 2) ≤ (a ^ k + b ^ k) / 2 * ((a + b) / 2) := by
      nlinarith [h_k]
    have h3 : (a ^ k + b ^ k) / 2 * ((a + b) / 2) ≤ (a ^ (k + 1) + b ^ (k + 1)) / 2 := by
      have h4 : (a ^ (k + 1) + b ^ (k + 1)) / 2 - (a ^ k + b ^ k) / 2 * ((a + b) / 2) ≥ 0 := by
        have h5 : (a ^ (k + 1) + b ^ (k + 1)) / 2 - (a ^ k + b ^ k) / 2 * ((a + b) / 2) = (a - b) * (a ^ k - b ^ k) / 4 := by
          ring_nf
        rw [h5]
        have h6 : (a - b) * (a ^ k - b ^ k) ≥ 0 := by
          by_cases h : a ≥ b
          · -- If a ≥ b
            have h7 : a ^ k ≥ b ^ k := by
              apply pow_le_pow_left
              all_goals linarith
            nlinarith
          · -- If a < b
            have h7 : a ^ k < b ^ k := by
              apply pow_lt_pow_left
              all_goals linarith
            nlinarith
        linarith
      linarith
    linarith
  exact Nat.le_induction base step n h4