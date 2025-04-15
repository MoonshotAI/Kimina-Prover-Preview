import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  
  have eq1 : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - x * y * (a * x + b * y) := by
    ring
  rw [h₀, h₁, h₂] at eq1
  
  have eq2 : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - x * y * (a * x ^ 2 + b * y ^ 2) := by
    ring
  rw [h₁, h₂, h₃] at eq2

  have h4 : (x + y) = -14 := by
    have eq1' : (x + y) * 7 - x * y * 3 = 16 := by linarith
    have eq2' : (x + y) * 16 - x * y * 7 = 42 := by linarith
    have h4 : (x + y) = -14 := by
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (a * x^2 - b * y^2), sq_nonneg (a * x - b * y)]
    linarith
  
  have h5 : x * y = -38 := by
    have eq1' : (x + y) * 7 - x * y * 3 = 16 := by linarith
    rw [h4] at eq1'
    linarith
    
  have h6 : a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - x * y * (a * x^3 + b * y^3) := by
    ring
  rw [h₃, h₂, h4, h5] at h6
  linarith