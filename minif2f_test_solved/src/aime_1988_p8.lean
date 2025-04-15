import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by
  have h1 : (14 + 52 : ℝ) * f 14 52 = 52 * f 14 66 := by
    specialize h₂ 14 52 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith
  
  have h2 : (14 + 38 : ℝ) * f 14 38 = 38 * f 14 52 := by
    specialize h₂ 14 38 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith

  have h3 : (14 + 24 : ℝ) * f 14 24 = 24 * f 14 38 := by
    specialize h₂ 14 24 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith

  have h4 : (14 + 10 : ℝ) * f 14 10 = 10 * f 14 24 := by
    specialize h₂ 14 10 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith
  
  have h5 : f 14 10 = f 10 14 := by
    specialize h₁ 14 10 ⟨by norm_num, by norm_num⟩
    linarith

  have h6 : (10 + 4 : ℝ) * f 10 4 = 4 * f 10 14 := by
    specialize h₂ 10 4 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith
  
  have h7 : f 10 4 = f 4 10 := by
    specialize h₁ 10 4 ⟨by norm_num, by norm_num⟩
    linarith

  have h8 : (4 + 6 : ℝ) * f 4 6 = 6 * f 4 10 := by
    specialize h₂ 4 6 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith

  have h9 : (4 + 2 : ℝ) * f 4 2 = 2 * f 4 6 := by
    specialize h₂ 4 2 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith

  have h10 : f 2 2 = (2 : ℝ) := by
    specialize h₀ 2 (by norm_num)
    norm_num at h₀
    linarith
  
  have h11 : (2 + 2 : ℝ) * f 2 2 = 2 * f 2 4 := by
    specialize h₂ 2 2 ⟨by norm_num, by norm_num⟩
    norm_num at h₂
    linarith
  
  have h12 : (f 2 4 : ℝ) = 4 := by 
    have h13 : (f 2 4 : ℝ) = 2 * f 2 2 := by
      linarith
    rw [h10] at h13
    linarith

  have h13 : f 4 2 = (4 : ℝ) := by 
    have h14 : f 4 2 = f 2 4 := by
      specialize h₁ 4 2 ⟨by norm_num, by norm_num⟩
      linarith
    rw [h14, h12]

  have h14 : (f 4 6 : ℝ) = 12 := by 
    have h15 : (6 : ℝ) * f 4 2 = 2 * f 4 6 := by
      linarith [h9]
    rw [h13] at h15
    linarith
  
  have h15 : (f 4 10 : ℝ) = 20 := by 
    have h16 : (10 : ℝ) * f 4 6 = 6 * f 4 10 := by
      linarith [h8]
    rw [h14] at h16
    linarith

  have h16 : (f 10 14 : ℝ) = 70 := by 
    have h17 : (14 : ℝ) * f 10 4 = 4 * f 10 14 := by
      linarith [h6]
    have h18 : f 10 4 = (20 : ℝ) := by
      linarith [h15, h7]
    rw [h18] at h17
    linarith

  have h17 : (f 14 24 : ℝ) = 168 := by 
    have h19 : (24 : ℝ) * f 14 10 = 10 * f 14 24 := by
      linarith [h4]
    have h20 : (f 14 10 : ℝ) = 70 := by
      linarith [h16, h5]
    rw [h20] at h19
    linarith

  have h18 : (f 14 38 : ℝ) = 266 := by 
    have h21 : (38 : ℝ) * f 14 24 = 24 * f 14 38 := by
      linarith [h3]
    rw [h17] at h21
    linarith
  
  have h19 : (f 14 52 : ℝ) = 364 := by 
    have h22 : (52 : ℝ) * f 14 38 = 38 * f 14 52 := by
      linarith [h2]
    rw [h18] at h22
    linarith

  exact h19