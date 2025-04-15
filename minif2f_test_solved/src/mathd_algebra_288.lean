import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
        have hy : y = -6 := by
            cases eq_or_eq_neg_of_abs_eq h₁ with
            | inl h => linarith [h₀.right]
            | inr h => linarith
        have h2' : (x - 8) ^ 2 + (y - 3) ^ 2 = 15 ^ 2 := by
            calc
                (x - 8) ^ 2 + (y - 3) ^ 2 = (Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
                _ = 15 ^ 2 := by rw [h₂]
        rw [hy] at h2'
        have hx_eq : x = -4 := by
            have h4 : (x - 8) ^ 2 = 144 := by
                nlinarith
            have h5 : x - 8 = 12 ∨ x - 8 = -12 := by
                apply eq_or_eq_neg_of_sq_eq_sq
                norm_num
                linarith
            cases h5 with
            | inl h12 =>
                have hx : x = 20 := by linarith
                linarith [h₀.left, hx]
            | inr h_neg12 =>
                have hx : x = -4 := by linarith
                exact hx
        have h3 : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = (n : ℝ) := by
            have h3_1 : Real.sqrt (x^2 + y^2) = Real.sqrt n := h₃
            have h3_2 : (x^2 + y^2 : ℝ) = (n : ℝ) := by
                have h4 : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = (Real.sqrt n) ^ 2 := by rw [h3_1]
                rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h4
                linarith
            exact_mod_cast h3_2
        rw [hx_eq, hy] at h3
        norm_num at h3
        have hn : (n : ℝ) = 52 := by linarith
        exact_mod_cast hn