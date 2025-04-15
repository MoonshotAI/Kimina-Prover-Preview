import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by 
        have h5 : x^2 - 10 * x - 29 ≠ 0 := h₁
        have h6 : x^2 - 10 * x - 45 ≠ 0 := h₂
        have h7 : x^2 - 10 * x - 69 ≠ 0 := h₃
        have h_eq : (x - 13) * (x + 3) = 0 := by
            field_simp [(show x^2 - 10 * x - 29 ≠ 0 by assumption), (show x^2 - 10 * x - 45 ≠ 0 by assumption), (show x^2 - 10 * x - 69 ≠ 0 by assumption)] at h₄
            ring_nf at h₄
            nlinarith [sq_nonneg (x - 13), sq_nonneg (x + 3), sq_nonneg (x^2 - 10 * x - 29), sq_nonneg (x^2 - 10 * x - 45), sq_nonneg (x^2 - 10 * x - 69)]
        cases' (mul_eq_zero.mp h_eq) with h13 h3
        · -- x - 13 = 0
          linarith
        · -- x + 3 = 0, so x = -3, contradicting 0 < x
          linarith