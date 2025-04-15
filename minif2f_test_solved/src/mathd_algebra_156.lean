import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have eq1 : x^4 = 5 * x^2 - 6 := by
    rw [h₀, h₁] at h₂
    linarith
  have eq2 : y^4 = 5 * y^2 - 6 := by
    rw [h₀, h₁] at h₃
    linarith

  have h5 : (x^2 - 2) * (x^2 - 3) = 0 := by
    have h1 : x^4 - 5 * x^2 + 6 = 0 := by linarith
    have h2 : x^4 - 5 * x^2 + 6 = (x^2 - 2) * (x^2 - 3) := by 
      ring
    nlinarith
  
  have h6 : (y^2 - 2) * (y^2 - 3) = 0 := by
    have h1 : y^4 - 5 * y^2 + 6 = 0 := by linarith
    have h2 : y^4 - 5 * y^2 + 6 = (y^2 - 2) * (y^2 - 3) := by 
      ring
    nlinarith

  have hx2 : x^2 = 2 ∨ x^2 = 3 := by
    cases (mul_eq_zero.mp h5) with
    | inl h => 
      left
      nlinarith 
    | inr h => 
      right
      nlinarith
  
  have hy2 : y^2 = 2 ∨ y^2 = 3 := by
    cases (mul_eq_zero.mp h6) with
    | inl h => 
      left
      nlinarith 
    | inr h => 
      right
      nlinarith

  cases hx2 with
  | inl hx2l =>
    cases hy2 with
    | inl hy2l =>
      exfalso
      nlinarith
    | inr hy2r =>
      have h : y^2 - x^2 = 1 := by
        rw [hy2r, hx2l]
        linarith
      linarith
  | inr hx2r =>
    cases hy2 with
    | inl hy2l =>
      exfalso
      nlinarith
    | inr hy2r =>
      exfalso
      nlinarith