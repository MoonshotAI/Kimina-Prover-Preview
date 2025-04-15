import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f (25 / 11) < 0 := by

  have f1 : f 1 = 0 := by
    specialize h₀ 1 (by norm_num) 1 (by norm_num)
    norm_num at h₀
    linarith

  have h25 : f (25 : ℚ) = (10 : ℝ) := by
    have h5 : f (5 : ℚ) = (5 : ℝ) := by
      specialize h₁ 5 (by norm_num)
      norm_num at h₁ ⊢
      exact h₁
    have h25_eq : (25 : ℚ) = ((5 : ℚ) * (5 : ℚ)) := by norm_num
    rw [h25_eq]
    specialize h₀ (5 : ℚ) (by norm_num) (5 : ℚ) (by norm_num)
    rw [h5] at h₀
    linarith

  have h11 : f (11 : ℚ) = (11 : ℝ) := by
    specialize h₁ 11 (by norm_num)
    norm_num at h₁ ⊢
    exact h₁

  have h25_11 : f (25 / 11 : ℚ) = f (25 : ℚ) + f (1 / 11 : ℚ) := by
    specialize h₀ (25 : ℚ) (by norm_num) (1 / 11 : ℚ) (by norm_num)
    rw [show (25 : ℚ) * (1 / 11 : ℚ) = (25 / 11 : ℚ) by norm_num] at h₀
    linarith
  
  have h1_11 : f (1 / 11 : ℚ) = -11 := by
    have h : f (1 : ℚ) = f (1 / 11 : ℚ) + f (11 : ℚ) := by
      specialize h₀ (1 / 11 : ℚ) (by norm_num) (11 : ℚ) (by norm_num)
      rw [show (1 / 11 : ℚ) * (11 : ℚ) = (1 : ℚ) by norm_num] at h₀
      linarith
    rw [f1, h11] at h
    linarith

  rw [h25_11, h25, h1_11]
  norm_num