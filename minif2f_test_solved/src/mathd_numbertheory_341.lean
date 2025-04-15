import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by 
  have h2 : 5 ^ 100 % 1000 = 625 := by
    norm_num
  
  have h3 : Nat.digits 10 625 = [5, 2, 6] := by 
    norm_num
  
  rw [h2] at h₁ 
  rw [h3] at h₁
  
  have hc : c = 5 := by 
    simp at h₁ 
    omega
  
  have hb : b = 2 := by 
    simp at h₁ 
    omega
  
  have ha : a = 6 := by 
    simp at h₁ 
    omega

  omega