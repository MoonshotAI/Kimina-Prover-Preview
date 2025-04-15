import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have h1 : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) = Real.log 80 * Real.log 40 / (Real.log 2 * Real.log 2) := by
    field_simp
    <;> ring
  have h2 : Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = Real.log 160 * Real.log 20 / (Real.log 2 * Real.log 2) := by
    field_simp
    <;> ring
  rw [h1, h2]
  have h3 : Real.log 80 = Real.log 16 + Real.log 5 := by
    rw [show (80 : ℝ) = 16 * 5 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have h4 : Real.log 40 = Real.log 8 + Real.log 5 := by
    rw [show (40 : ℝ) = 8 * 5 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have h5 : Real.log 160 = Real.log 32 + Real.log 5 := by
    rw [show (160 : ℝ) = 32 * 5 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have h6 : Real.log 20 = Real.log 4 + Real.log 5 := by
    rw [show (20 : ℝ) = 4 * 5 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have h7 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num]
    simp [Real.log_pow]
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
    simp [Real.log_pow]
  have h9 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num]
    simp [Real.log_pow]
  have h10 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    simp [Real.log_pow]
  have h11 : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by linarith [h3, h7]
  have h12 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by linarith [h4, h8]
  have h13 : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by linarith [h5, h9]
  have h14 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by linarith [h6, h10]
  have h15 : Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20 = 2 * (Real.log 2 * Real.log 2) := by
    rw [h11, h12, h13, h14]
    ring
  have h16 : Real.log 2 ≠ 0 := by 
    have h_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have h17 : (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) / (Real.log 2 * Real.log 2) = 2 := by
    have h18 : Real.log 2 * Real.log 2 ≠ 0 := by
      apply mul_ne_zero
      · exact h16
      · exact h16
    field_simp [h18]
    linarith [h15]
  have h19 : Real.log 80 * Real.log 40 / (Real.log 2 * Real.log 2) - Real.log 160 * Real.log 20 / (Real.log 2 * Real.log 2) = 2 := by
    have h20 : Real.log 80 * Real.log 40 / (Real.log 2 * Real.log 2) - Real.log 160 * Real.log 20 / (Real.log 2 * Real.log 2) = 
      (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) / (Real.log 2 * Real.log 2) := by
      ring
    rw [h20]
    exact h17
  linarith [h19]