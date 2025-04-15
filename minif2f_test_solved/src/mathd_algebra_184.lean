import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 := by

  have hb : b = 3 := by
    have h_pos : 0 < b := h₀.right
    have eq1 : a ^ 2 = 6 * b := h₁
    have eq2 : a ^ 2 = 54 / b := h₂
    have h3 : (6 * b : ℝ) = (54 / b : ℝ) := by
      have h4 : (a ^ 2 : ℝ) = (6 * b : ℝ) := by
        exact_mod_cast eq1
      have h5 : (a ^ 2 : ℝ) = (54 / b : ℝ) := by
        exact_mod_cast eq2
      rw [h4] at h5
      linarith
    have h4 : (b : ℝ) ≠ 0 := by
      have h5 : (b : ℝ) > 0 := by exact_mod_cast h_pos
      linarith
    have h5 : (b : ℝ) ^ 2 = 9 := by
      have h6 : (6 * b : ℝ) = (54 / b : ℝ) := by
        exact_mod_cast h3
      field_simp at h6
      nlinarith [h4]
    have h6 : (b : ℝ) = 3 := by
      have h7 : (b : ℝ) > 0 := by exact_mod_cast h_pos
      have h8 : (b : ℝ) = 3 := by
        have h9 : (b : ℝ) ^ 2 - 9 = 0 := by linarith
        have h10 : ((b : ℝ) - 3) * ((b : ℝ) + 3) = 0 := by
          rw [←h9]
          ring
        cases' (mul_eq_zero.mp h10) with h11 h12
        · -- (b : ℝ) - 3 = 0
          linarith
        · -- (b : ℝ) + 3 = 0
          have h13 : (b : ℝ) = -3 := by linarith
          linarith [h7, h13]
      exact h8
    exact_mod_cast h6
    all_goals linarith

  have ha_sq : a ^ 2 = 18 := by
    have h1 : a ^ 2 = 6 * b := h₁
    rw [hb] at h1
    have h2 : a ^ 2 = 18 := by
      have h3 : (a ^ 2 : ℝ) = (6 * (3 : ℝ) : ℝ) := by
        exact_mod_cast h1
      norm_num at h3
      exact_mod_cast h3
    exact h2

  have ha : a = 3 * NNReal.sqrt 2 := by
    have h_pos : 0 < a := h₀.left
    have h1 : a ^ 2 = 18 := ha_sq
    have h2 : a = NNReal.sqrt 18 := by
      rw [←h1]
      field_simp [h_pos]
    rw [h2]
    have h3 : NNReal.sqrt 18 = 3 * NNReal.sqrt 2 := by
      rw [NNReal.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
      <;> positivity
    rw [h3]

  exact ha