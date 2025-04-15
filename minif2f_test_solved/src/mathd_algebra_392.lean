import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by 
  have h2 : (n : ℤ) ^ 2 = 4096 := by
    ring_nf at h₁
    nlinarith
  
  have hn : (n : ℤ) = 64 := by 
    have h3 : (n : ℤ) ^ 2 - 4096 = 0 := by linarith
  
    have h4 : ((n : ℤ) - 64) * ((n : ℤ) + 64) = 0 := by 
      ring_nf at h3 ⊢ 
      linarith
  
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- n - 64 = 0 
      linarith 
    · -- n + 64 = 0 
      have h7 : (n : ℤ) = -64 := by linarith 
      have h8 : n = 0 := by 
        norm_num at h7 
        omega 
      have h9 : n ≥ 2 := by 
        rcases h₀ with ⟨k, hk⟩ 
        omega 
      omega
  
  rw [hn]
  norm_num