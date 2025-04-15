import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h1 : x + y + z > 0 := by nlinarith [h₀.left, h₀.right.left, h₀.right.right]
  have h2 : x + y > 0 := by nlinarith [h₀.left, h₀.right.left]
  have h3 : y + z > 0 := by nlinarith [h₀.right.left, h₀.right.right]
  have h4 : z + x > 0 := by nlinarith [h₀.left, h₀.right.right]
  have h5 : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    have h6 : (x + y) * (y + z) * (z + x) > 0 := by
      apply mul_pos
      apply mul_pos
      nlinarith
      nlinarith
      nlinarith
    have h7 : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
      have h8 : 9 / (x + y + z) - (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≤ 0 := by
        have h9 : (x + y + z) > 0 := h1
        have h10 : (x + y) > 0 := h2
        have h11 : (y + z) > 0 := h3
        have h12 : (z + x) > 0 := h4
        have h13 : 9 / (x + y + z) - (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) =
          (9 * ((x + y) * (y + z) * (z + x)) - 2 * (x + y + z) * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z))) / ((x + y + z) * (x + y) * (y + z) * (z + x)) := by
          field_simp
          ring
        rw [h13]
        have h14 : 9 * ((x + y) * (y + z) * (z + x)) - 2 * (x + y + z) * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) ≤ 0 := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (y + z - x),
            mul_pos h2 h3, mul_pos h3 h4, mul_pos h4 h2]
        have h15 : (x + y + z) * (x + y) * (y + z) * (z + x) > 0 := by
          apply mul_pos
          apply mul_pos
          apply mul_pos
          all_goals linarith
        apply (div_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)).trans
        · norm_num
        all_goals linarith
      linarith
    linarith
  exact h5