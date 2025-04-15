import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2021_p3 (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) : x = 3 / 4 := by
  have h1 : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 := h₀
  have h2 : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 - 2 := by
    linarith
  have h3 : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := by
    have h2' : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 - 2 := by linarith
    have h_pos : 1 + 1 / (2 + 2 / (3 + x)) ≠ 0 := by
      by_contra h
      rw [h] at h2'
      norm_num at h2'
    field_simp [h_pos] at h2'
    linarith
  have h4 : 1 / (2 + 2 / (3 + x)) = 15 / 38 := by
    linarith
  have h5 : 2 + 2 / (3 + x) = 38 / 15 := by
    have h4' : 1 / (2 + 2 / (3 + x)) = 15 / 38 := by linarith
    have h_pos2 : 2 + 2 / (3 + x) ≠ 0 := by
      by_contra h
      rw [h] at h4'
      norm_num at h4'
    field_simp [h_pos2] at h4'
    linarith
  have h6 : 2 / (3 + x) = 8 / 15 := by
    have h5' : 2 + 2 / (3 + x) = 38 / 15 := by linarith
    linarith
  have h7 : 3 + x ≠ 0 := by
    by_contra h
    rw [h] at h6
    norm_num at h6
  have h8 : 2 = 8 / 15 * (3 + x) := by
    field_simp [h7] at h6
    linarith
  have h9 : x = 3 / 4 := by
    linarith
  exact h9