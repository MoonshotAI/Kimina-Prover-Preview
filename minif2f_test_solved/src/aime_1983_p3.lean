import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (h₁ : Fintype (f ⁻¹' {0})) : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by
  have h2 : (f ⁻¹' {0}).toFinset = {-9 + Real.sqrt 61, -9 - Real.sqrt 61} := by
    ext x
    simp [h₀]
    constructor
    · -- Assume f(x) = 0, prove x ∈ {-9 + √61, -9 - √61}
      intro hx
      have h1 : x ^ 2 + (18 * x + 30) = 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) := by linarith
      have h2 : Real.sqrt (x ^ 2 + (18 * x + 45)) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + (18 * x + 45))
      have h3 : x ^ 2 + (18 * x + 30) ≥ 0 := by linarith [h2, h1]
      have h4 : (x ^ 2 + (18 * x + 30)) ^ 2 = (2 * Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 := by
        rw [h1]
      have h5 : (x ^ 2 + (18 * x + 30)) ^ 2 = 4 * (x ^ 2 + (18 * x + 45)) := by
        have h5 : (2 * Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 = 4 * (Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 := by ring
        have h6 : (Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 = x ^ 2 + (18 * x + 45) := Real.sq_sqrt (by nlinarith)
        nlinarith [h4, h5, h6]
      have h6 : (x ^ 2 + (18 * x + 30)) ^ 2 - 4 * (x ^ 2 + (18 * x + 45)) = 0 := by linarith
      have h7 : (x^2 + 18 * x + 20) * (x^2 + 18 * x + 36) = 0 := by
        ring_nf at h6 ⊢
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case x^2 + 18x + 20 = 0
        have h10 : x ^ 2 + 18 * x + 20 = 0 := by linarith
        have h11 : (x - (-9 + Real.sqrt 61)) * (x - (-9 - Real.sqrt 61)) = 0 := by
          have h12 : (x - (-9 + Real.sqrt 61)) * (x - (-9 - Real.sqrt 61)) = x^2 + 18 * x + 20 := by
            ring_nf
            have h13 : Real.sqrt 61 ^ 2 = 61 := Real.sq_sqrt (by norm_num)
            linarith [h13]
          rw [h12]
          linarith
        cases' (mul_eq_zero.mp h11) with h14 h15
        · -- x - (-9 + √61) = 0
          left
          linarith
        · -- x - (-9 - √61) = 0
          right
          linarith
      · -- Case x^2 + 18x + 36 = 0
        have h16 : x ^ 2 + 18 * x + 36 = 0 := by linarith
        have h17 : x ^ 2 + (18 * x + 30) = -6 := by linarith
        have h18 : 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = -6 := by linarith [h1, h17]
        have h19 : Real.sqrt (x ^ 2 + (18 * x + 45)) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + (18 * x + 45))
        have h20 : Real.sqrt (x ^ 2 + (18 * x + 45)) ≤ 0 := by linarith [h18]
        have h21 : Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by linarith [h19, h20]
        have h22 : Real.sqrt (x ^ 2 + (18 * x + 45)) = -3 := by linarith [h18]
        linarith [h19, h22]
    · -- Assume x ∈ {-9 + √61, -9 - √61}, prove f(x) = 0
      rintro (h1 | h2)
      · -- x = -9 + √61
        rw [h1]
        have h3 : Real.sqrt 61 ^ 2 = 61 := Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)
        have h4 : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 30) - 2 * Real.sqrt ((-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) = 0 := by
          have h6 : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 30) = 10 := by
            ring_nf
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
          have h7 : Real.sqrt ((-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) = 5 := by
            have h8 : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45) = 25 := by
              ring_nf
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
            rw [h8]
            exact Real.sqrt_eq_cases.2 (by norm_num)
          linarith [h6, h7]
        linarith [h4]
      · -- x = -9 - √61
        rw [h2]
        have h3 : Real.sqrt 61 ^ 2 = 61 := Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)
        have h4 : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 30) - 2 * Real.sqrt ((-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) = 0 := by
          have h6 : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 30) = 10 := by
            ring_nf
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
          have h7 : Real.sqrt ((-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) = 5 := by
            have h8 : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45) = 25 := by
              ring_nf
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
            rw [h8]
            exact Real.sqrt_eq_cases.2 (by norm_num)
          linarith [h6, h7]
        linarith [h4]
  rw [h2]
  have h3 : (-9 + Real.sqrt 61) ≠ (-9 - Real.sqrt 61) := by
    have h4 : Real.sqrt 61 > 0 := Real.sqrt_pos.mpr (by norm_num)
    linarith [h4]
  simp [Finset.prod_insert, Finset.prod_singleton, h3]
  <;> ring_nf <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]