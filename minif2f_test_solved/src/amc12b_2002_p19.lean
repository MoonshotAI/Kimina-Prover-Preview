import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by

  have pos_a : 0 < a := h₀.1
  have pos_b : 0 < b := h₀.2.1
  have pos_c : 0 < c := h₀.2.2

  have eq1 : a * b + a * c = 152 := by linarith

  have eq2 : b * a + b * c = 162 := by linarith

  have eq3 : c * a + c * b = 170 := by linarith

  have h4 : a * b = 72 := by
    nlinarith [mul_pos pos_a pos_b, mul_pos pos_b pos_c, mul_pos pos_a pos_c, eq1, eq2, eq3]

  have h5 : b * c = 90 := by
    nlinarith [mul_pos pos_a pos_b, mul_pos pos_b pos_c, mul_pos pos_a pos_c, eq1, eq2, eq3]

  have h6 : a * c = 80 := by
    nlinarith [mul_pos pos_a pos_b, mul_pos pos_b pos_c, mul_pos pos_a pos_c, eq1, eq2, eq3]

  have h7 : a * b * c = 720 := by
    nlinarith [mul_pos pos_a pos_b, mul_pos pos_b pos_c, mul_pos pos_a pos_c, h4, h5, h6]

  exact h7