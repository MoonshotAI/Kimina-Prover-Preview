import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have h2 : (m : ℝ) / (a : ℝ) = (3 : ℝ) / 4 := by
    exact_mod_cast h₁
  have h3 : (a : ℝ) ≠ 0 := by
    have ha : (a : ℝ) > (0 : ℝ) := by
      exact_mod_cast h₀.right
    linarith
  have h4 : (m : ℝ) = (3 : ℝ) / 4 * (a : ℝ) := by
    have h5 : (a : ℝ) ≠ 0 := h3
    field_simp at h2 ⊢
    linarith
  have h5 : (↑m + ↑a : ℝ) ≠ 0 := by
    have ha : (a : ℝ) > 0 := by exact_mod_cast h₀.right
    have hm : (m : ℝ) ≥ 0 := by
      exact_mod_cast (show (m : ℝ) ≥ (0 : ℝ) by norm_num)
    nlinarith [h4]
  have h6 : (84 : ℝ) * ↑m + 70 * ↑a = 76 * (↑m + ↑a) := by
    have h7 : (m : ℝ) = (3 : ℝ) / 4 * (a : ℝ) := h4
    linarith
  have h8 : (84 * (m : ℝ) + 70 * (a : ℝ)) / ((m : ℝ) + (a : ℝ)) = (76 : ℝ) := by
    have h9 : (84 : ℝ) * ↑m + 70 * ↑a = 76 * (↑m + ↑a) := h6
    have h10 : (↑m + ↑a : ℝ) ≠ 0 := by
      exact_mod_cast h5
    field_simp at *
    linarith
  exact h8