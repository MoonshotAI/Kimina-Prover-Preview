import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have h2 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul]
    all_goals linarith
  have h3 : 0 < b := h₀.right
  have h4 : 0 < a := h₀.left
  have h5 : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
    have h6 : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
      rw [h2]
      have h7 : Real.sqrt a ^ 2 = a := by
        rw [Real.sq_sqrt]
        linarith
      have h8 : Real.sqrt b ^ 2 = b := by
        rw [Real.sq_sqrt]
        linarith
      have h9 : (Real.sqrt a - Real.sqrt b) ^ 2 = (Real.sqrt a) ^ 2 - 2 * (Real.sqrt a * Real.sqrt b) + (Real.sqrt b) ^ 2 := by ring
      rw [h9]
      have h10 : (Real.sqrt a) ^ 2 - 2 * (Real.sqrt a * Real.sqrt b) + (Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt a * Real.sqrt b := by
        have h11 : (Real.sqrt a) ^ 2 = a := by
          exact h7
        have h12 : (Real.sqrt b) ^ 2 = b := by
          exact h8
        have h13 : Real.sqrt a * Real.sqrt b = Real.sqrt a * Real.sqrt b := by rfl
        linarith [h11, h12]
      linarith [h10, h7, h8]
    have h10 : (a - b) ^ 2 / (8 * b) = ((Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2) / (8 * b) := by
      have hsqab2 : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
        have h1 : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
          calc
            (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)
              = (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 := by ring
            _ = a - b := by
              have h2 : (Real.sqrt a) ^ 2 = a := by
                exact Real.sq_sqrt (by linarith)
              have h3 : (Real.sqrt b) ^ 2 = b := by
                exact Real.sq_sqrt (by linarith)
              linarith [h2, h3]
        have h2 : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)) ^ 2 := by
          ring
        rw [h2]
        have h3 : ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)) ^ 2 = (a - b) ^ 2 := by
          rw [h1]
        linarith [h3]
      field_simp
      nlinarith [hsqab2]
    rw [h6, h10]
    have h11 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h12 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h13 : 0 ≤ Real.sqrt a + Real.sqrt b := by
      linarith [h11, h12]
    have h14 : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := by
      apply sq_nonneg
    have h15 : (Real.sqrt a + Real.sqrt b) ^ 2 ≥ 4 * b := by
      have h16 : Real.sqrt a ≥ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith),
        mul_self_nonneg (Real.sqrt a - Real.sqrt b), h16]
    have h17 : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 * ((Real.sqrt a + Real.sqrt b) ^ 2 - 4 * b) := by
      apply mul_nonneg
      · exact h14
      · linarith [h15]
    have h18 : 0 ≤ 8 * b := by
      linarith [h3]
    have h19 : (Real.sqrt a - Real.sqrt b) ^ 2 * ((Real.sqrt a + Real.sqrt b) ^ 2 - 4 * b) / (8 * b) ≥ 0 := by
      apply div_nonneg
      · exact h17
      · linarith [h18]
    have h20 : (Real.sqrt a - Real.sqrt b) ^ 2 / 2 ≤ ((Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2) / (8 * b) := by
      have h22 : ((Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2) / (8 * b) - (Real.sqrt a - Real.sqrt b) ^ 2 / 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * ((Real.sqrt a + Real.sqrt b) ^ 2 - 4 * b) / (8 * b) := by
        field_simp
        ring
      have h21 : (Real.sqrt a - Real.sqrt b) ^ 2 * ((Real.sqrt a + Real.sqrt b) ^ 2 - 4 * b) / (8 * b) ≥ 0 := by
        apply div_nonneg
        · exact h17
        · linarith [h18]
      linarith [h22, h21]
    linarith [h20]
  linarith [h5]