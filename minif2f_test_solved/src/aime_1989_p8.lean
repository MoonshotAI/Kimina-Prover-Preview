import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1989_p8 (a b c d e f g : ℝ)
    (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
    (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
    (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
    16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
  
  have eq1 : 3 * a + 5 * b + 7 * c + 9 * d + 11 * e + 13 * f + 15 * g = 11 := by 
    linarith
  
  have eq2 : 5 * a + 7 * b + 9 * c + 11 * d + 13 * e + 15 * f + 17 * g = 111 := by 
    linarith

  have h_sum : a + b + c + d + e + f + g = 50 := by
    have temp : 2 * a + 2 * b + 2 * c + 2 * d + 2 * e + 2 * f + 2 * g = 100 := by 
      linarith [eq1, eq2]
    linarith

  have eq3 : 7 * a + 9 * b + 11 * c + 13 * d + 15 * e + 17 * f + 19 * g = 211 := by 
    linarith [eq2, h_sum]

  have h3 : 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by 
    linarith [h₂, eq3]

  exact h3