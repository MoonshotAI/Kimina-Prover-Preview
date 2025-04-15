import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  have h3 : 0 ≤ Real.sqrt (1 + 2 * x) := Real.sqrt_nonneg (1 + 2 * x)
  have h4 : (1 - Real.sqrt (1 + 2 * x)) ≠ 0 := by
    intro h
    have : (1 - Real.sqrt (1 + 2 * x)) ^ 2 = 0 := by
      rw [h]
      ring
    contradiction
  have h5 : (1 - Real.sqrt (1 + 2 * x)) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    exact h4
  have h6 : 4 * x^2 < (2 * x + 9) * (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by
    have h_pos : 0 < (1 - Real.sqrt (1 + 2 * x)) ^ 2 := by linarith
    apply (div_lt_iff h_pos).mp at h₂
    nlinarith
  have h8 : x < 45 / 8 := by
    by_contra h
    push_neg at h
    have h9 : Real.sqrt (1 + 2 * x) ≥ 7 / 2 := by
      have h10 : 1 + 2 * x ≥ (7 / 2) ^ 2 := by
        nlinarith [h]
      have h11 : Real.sqrt (1 + 2 * x) ≥ Real.sqrt ((7 / 2) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have h12 : Real.sqrt ((7 / 2) ^ 2) = 7 / 2 := by
        rw [Real.sqrt_sq]
        all_goals linarith
      linarith
    have h13 : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≥ (5 / 2) ^ 2 := by
      nlinarith [h9, Real.sqrt_nonneg (1 + 2 * x)]
    nlinarith [h6, h13, sq_nonneg (Real.sqrt (1 + 2 * x)), sq_nonneg (x - 45 / 8), Real.sq_sqrt (show 0 ≤ 1 + 2 * x by linarith)]
  have h14 : -(1 / 2) ≤ x := by linarith
  exact ⟨h14, h8⟩