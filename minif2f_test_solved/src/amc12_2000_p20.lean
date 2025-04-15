import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  have pos_x : 0 < x := h₀.left
  have pos_y : 0 < y := h₀.right.left
  have pos_z : 0 < z := h₀.right.right
  have eq1 : x * y + 1 = 4 * y := by 
    field_simp at h₁
    nlinarith
  have eq2 : y * z + 1 = z := by 
    field_simp at h₂
    nlinarith [pos_z]
  have eq3 : z * x + 1 = (7 / 3) * x := by 
    field_simp at h₃
    nlinarith [pos_x]
  have sum_eq : x + 1 / y + y + 1 / z + z + 1 / x = 22 / 3 := by
    have h1 := h₁
    have h2 := h₂
    have h3 := h₃
    have h4 : x + 1 / y + (y + 1 / z) + (z + 1 / x) = 4 + 1 + (7 / 3 : ℝ) := by
      linarith [h₁, h₂, h₃]
    have h5 : x + 1 / y + (y + 1 / z) + (z + 1 / x) = x + 1 / y + y + 1 / z + z + 1 / x := by
      ring
    rw [h5] at h4
    linarith
  have h4 : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = 4 * 1 * (7 / 3 : ℝ) := by
    rw [h₁, h₂, h₃]
  have eq4 : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = x * y * z + (x + 1 / y + y + 1 / z + z + 1 / x) + 1 / (x * y * z) := by
    field_simp
    ring_nf
  rw [eq4] at h4
  have eq5 : x * y * z + 1 / (x * y * z) = 2 := by
    have h_sum : x + 1 / y + y + 1 / z + z + 1 / x = 22 / 3 := sum_eq
    have h_eq : x * y * z + (x + 1 / y + y + 1 / z + z + 1 / x) + 1 / (x * y * z) = 28 / 3 := by
      linarith
    rw [h_sum] at h_eq
    have h : x * y * z + 1 / (x * y * z) = 2 := by
      linarith
    exact h
  have pos_xyz : x * y * z ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    · linarith
    · linarith
    · linarith
  have h5 : x * y * z = 1 := by
    have h6 : x * y * z = 1 := by
      have h7 : x * y * z > 0 := by
        apply mul_pos
        apply mul_pos
        · linarith
        · linarith
        · linarith
      have h8 : x * y * z > 0 := h7
      have h9 : x * y * z ≠ 0 := pos_xyz
      have h10 : (x * y * z - 1) ^ 2 = 0 := by
        have h11 : x * y * z + 1 / (x * y * z) = 2 := eq5
        field_simp at h11
        nlinarith [sq_nonneg (x * y * z - 1)]
      have h12 : x * y * z - 1 = 0 := by
        rw [sq_eq_zero_iff] at h10
        exact h10
      linarith
    exact h6
  exact h5