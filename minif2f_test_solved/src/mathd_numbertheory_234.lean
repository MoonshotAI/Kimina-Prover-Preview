import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by

  have h2 : a ≤ 9 := h₀.right.left
  have h3 : b ≤ 9 := h₀.right.right
  
  have h4 : 10 * a + b = 97 := by
    have h5 : 10 * a + b ≤ 99 := by 
      omega
    have h6 : 10 * a + b ≥ 10 := by
      omega

    have h7 : 10 * a + b = 97 := by
      interval_cases h11 : (10 * a + b) <;> omega

    exact h7

  have h12 : a = 9 := by 
    omega
  
  have h13 : b = 7 := by 
    omega

  calc 
    a + b = 9 + 7 := by rw [h12, h13]
    _ = 16 := by norm_num