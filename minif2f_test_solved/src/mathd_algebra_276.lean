import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 := by
        have h1 := h₀ 0
        have h2 := h₀ 1
        have h3 := h₀ (-1)
        have h4 := h₀ 2
        norm_num at h1 h2 h3 h4
        have hab : a * b = 10 := by
          have h2_real : (a : ℝ) * (b : ℝ) = 10 := by
            nlinarith
          exact_mod_cast h2_real
        have h_eq : 3 * a - 8 * b = -1 := by
          have h3_real : (3 : ℝ) * (a : ℝ) - 8 * (b : ℝ) = -1 := by
            nlinarith [h2, h3]
          have h3_int : (3 : ℤ) * a - 8 * b = -1 := by
            have h3_real := h3_real
            norm_cast at h3_real
            <;> linarith
          linarith
        have ha : a = 5 := by
          have h1 : a ≤ 10 := by 
            nlinarith [hab]
          have h2 : a ≥ -10 := by 
            nlinarith [hab]
          interval_cases a <;> omega
        have hb : b = 2 := by
          rw [ha] at h_eq
          omega
        rw [ha, hb]
        norm_num