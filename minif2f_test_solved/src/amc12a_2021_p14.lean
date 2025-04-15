import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2021_p14 :
    ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = 21000 := by

  have h1 : (∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) = (210 : ℝ) * (Real.logb 5 3) := by
    simp [Finset.sum_Icc_succ_top, Real.logb]
    <;> ring_nf <;> field_simp <;> ring
    <;> norm_num

  have h2 : (∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = (100 : ℝ) * (Real.logb 9 25) := by
    simp [Finset.sum_Icc_succ_top, Real.logb]
    <;> ring_nf <;> field_simp <;> ring
    <;> norm_num

  rw [h1, h2]
  
  have h3 : Real.logb 9 25 = Real.logb 3 5 := by
    have h31 : Real.logb 9 25 = Real.log 25 / Real.log 9 := by
      simp [Real.logb]
    have h32 : Real.logb 3 5 = Real.log 5 / Real.log 3 := by
      simp [Real.logb]
    rw [h31, h32]
    have h33 : Real.log 25 = 2 * Real.log 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
      simp [Real.log_pow]
    have h34 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      simp [Real.log_pow]
    rw [h33, h34]
    ring
  
  rw [h3]
  have h4 : Real.logb 5 3 * Real.logb 3 5 = 1 := by
    have h41 : Real.logb 5 3 = Real.log 3 / Real.log 5 := by
      simp [Real.logb]
    have h42 : Real.logb 3 5 = Real.log 5 / Real.log 3 := by
      simp [Real.logb]
    rw [h41, h42]
    field_simp

  have h5 : (210 : ℝ) * Real.logb 5 3 * (100 : ℝ) * Real.logb 3 5 = 21000 := by
    have h51 : (210 : ℝ) * Real.logb 5 3 * (100 : ℝ) * Real.logb 3 5 = 
        (210 * 100 : ℝ) * (Real.logb 5 3 * Real.logb 3 5) := by ring
    rw [h51]
    have h52 : Real.logb 5 3 * Real.logb 3 5 = 1 := by 
      linarith [h4]
    rw [h52]
    norm_num
  
  linarith [h5]