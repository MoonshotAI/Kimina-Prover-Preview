import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
        have h1 : ∀ x : ℝ, 0 ≤ f x ∧ f x ≤ 1 := by
            intro x
            have h2 := h₁ (x - a)
            have h2' := h₁ x
            have h3 : 0 ≤ Real.sqrt (f (x - a) - f (x - a) ^ 2) := Real.sqrt_nonneg (f (x - a) - f (x - a) ^ 2)
            have h4 : f (x) ≥ 1 / 2 := by
                have h5 : f (x) = 1 / 2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
                    rw [show x - a + a = (x : ℝ) by ring] at h2
                    linarith
                linarith [h3]
            have h5 : f (x) ≤ 1 := by
                have h6 : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ 1 / 2 := by
                    have h7 : f (x - a) - f (x - a) ^ 2 ≤ (1 / 4 : ℝ) := by
                        have h8 : (f (x - a) - 1 / 2) ^ 2 ≥ 0 := by
                            exact sq_nonneg (f (x - a) - 1 / 2)
                        nlinarith [sq_nonneg (f (x - a) - 1 / 2)]
                    have h9 : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ Real.sqrt (1 / 4 : ℝ) := Real.sqrt_le_sqrt h7
                    have h10 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
                        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
                        rw [Real.sqrt_sq]
                        all_goals norm_num
                    linarith [h10]
                have h7 : f x = 1 / 2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
                    rw [show x - a + a = (x : ℝ) by ring] at h2
                    linarith
                linarith [h6, h7]
            constructor
            · linarith [h4]
            · linarith [h5]
        use 2 * a
        constructor
        · linarith [h₀]
        · intro x
          have h2 := h₁ (x + a)
          have h3 := h₁ x
          have h4 : f (x + 2 * a) = 1 / 2 + Real.sqrt (f (x + a) - f (x + a) ^ 2) := by
            rw [show x + 2 * a = (x + a) + a by ring]
            linarith [h2]
          have h5 : f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2) := by
            linarith [h3]
          have h6 : f (x + a) - f (x + a) ^ 2 = (f x - 1 / 2) ^ 2 := by
            rw [h5]
            ring_nf
            <;> nlinarith [Real.sq_sqrt (show 0 ≤ f x - f x ^ 2 by nlinarith [h1 x]), h1 x]
          rw [h6] at h4
          have h7 : Real.sqrt ((f x - 1 / 2) ^ 2) = |f x - 1 / 2| := by
            rw [Real.sqrt_sq_eq_abs]
          rw [h7] at h4
          have h8 : f x - 1 / 2 ≥ 0 := by
            have h9 := h₁ (x - a)
            have h10 : f x = 1 / 2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
              rw [show x - a + a = (x : ℝ) by ring] at h9
              linarith
            have h11 : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≥ 0 := Real.sqrt_nonneg (f (x - a) - f (x - a) ^ 2)
            linarith [h10, h11]
          rw [abs_of_nonneg h8] at h4
          linarith [h4]