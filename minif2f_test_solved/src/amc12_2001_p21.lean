import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12_2001_p21 (a b c d : ℕ) (h₀ : a * b * c * d = 8!) (h₁ : a * b + a + b = 524)
    (h₂ : b * c + b + c = 146) (h₃ : c * d + c + d = 104) : ↑a - ↑d = (10 : ℤ) := by

  have h4 : (a + 1) * (b + 1) = 525 := by nlinarith
  have h5 : (b + 1) * (c + 1) = 147 := by nlinarith
  have h6 : (c + 1) * (d + 1) = 105 := by nlinarith
  
  have h7 : b + 1 ≤ 525 := by nlinarith
  have h8 : c + 1 ≤ 147 := by nlinarith
  have h9 : d + 1 ≤ 105 := by nlinarith
  
  have h10 : b + 1 ≤ 147 := by nlinarith
  
  have h11 : (b + 1) ∣ 21 := by 
    have h4a : (b + 1) ∣ 525 := by
      use a + 1
      nlinarith
    have h5a : (b + 1) ∣ 147 := by
      use c + 1
      nlinarith
    have h11 : (b + 1) ∣ Nat.gcd 525 147 := by
      apply Nat.dvd_gcd h4a h5a
    rw [show Nat.gcd 525 147 = 21 by norm_num] at h11
    exact h11
  
  have h12 : b + 1 ≤ 21 := by 
    exact Nat.le_of_dvd (by norm_num) h11
  
  have h13 : b + 1 = 1 ∨ b + 1 = 3 ∨ b + 1 = 7 ∨ b + 1 = 21 := by
    interval_cases hb1 : b + 1 <;> norm_num at h11 <;> omega
  
  rcases h13 with (h21 | h23 | h27 | h221)

  · -- Case b + 1 = 1
    have hc1 : c + 1 = 147 := by 
      rw [h21] at h5
      omega
    have hd1 : d + 1 = 0 := by 
      rw [hc1] at h6
      omega
    have h_d : d = 0 := by omega
    have h_d1 : d ≥ 0 := by omega
    omega

  · -- Case b + 1 = 3
    have hc1 : c + 1 = 49 := by 
      rw [h23] at h5
      omega
    have hd1 : d + 1 = 0 := by 
      rw [hc1] at h6
      omega
    have h_d : d = 0 := by omega
    have h_d1 : d ≥ 0 := by omega
    omega

  · -- Case b + 1 = 7
    have hc1 : c + 1 = 21 := by 
      rw [h27] at h5
      omega
    have hd1 : d + 1 = 5 := by 
      rw [hc1] at h6
      omega
    have h_d : d = 4 := by omega
    have ha1 : a + 1 = 75 := by 
      rw [h27] at h4
      omega
    have h_a : a = 74 := by omega
    have h74 : a * b * c * d = 40320 := by 
      calc 
        a * b * c * d = 8! := h₀
        _ = 40320 := by rfl
    have h75 : a * b * c * d = 74 * 6 * 20 * 4 := by
      rw [h_a]
      have hb : b = 6 := by omega
      have hc : c = 20 := by omega
      rw [hb, hc, h_d]
    norm_num at h75
    omega

  · -- Case b + 1 = 21
    have hc1 : c + 1 = 7 := by 
      rw [h221] at h5
      omega
    have hd1 : d + 1 = 15 := by 
      rw [hc1] at h6
      omega
    have h_d : d = 14 := by omega
    have ha1 : a + 1 = 25 := by 
      rw [h221] at h4
      omega
    have h_a : a = 24 := by omega
    have h_diff : (a : ℤ) - (d : ℤ) = 10 := by 
      rw [h_a, h_d]
      norm_num
    exact h_diff