import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by 
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨k, hk⟩
  have ha : a ^ 2 % 8 = 1 := by
    rw [hm]
    have h : (2 * m + 1) ^ 2 % 8 = 1 := by 
      have h1 : (2 * m + 1) % 8 = 1 ∨ (2 * m + 1) % 8 = 3 ∨ (2 * m + 1) % 8 = 5 ∨ (2 * m + 1) % 8 = 7 := by 
        have h2 : m % 2 = 0 ∨ m % 2 = 1 := by 
          omega
        rcases h2 with (h2 | h2) <;> ( 
          have : (2 * m + 1) % 8 = 1 ∨ (2 * m + 1) % 8 = 3 ∨ (2 * m + 1) % 8 = 5 ∨ (2 * m + 1) % 8 = 7 := by 
            omega
          assumption
        )
      rcases h1 with (h1 | h1 | h1 | h1) <;> ( 
        norm_num [h1, pow_two, Int.add_emod, Int.mul_emod] 
      )
    exact h
  have hb : (b : ℤ) ^ 2 % 8 = 0 := by 
    have h4 : (b : ℤ) = 4 * (k : ℤ) := by 
      norm_num [hk]
    rw [h4]
    have h5 : (4 * (k : ℤ)) ^ 2 % 8 = 0 := by 
      have h6 : (4 * (k : ℤ)) ^ 2 = 16 * (k : ℤ) ^ 2 := by 
        ring
      rw [h6]
      omega
    exact h5
  have h2 : (a ^ 2 + (b : ℤ) ^ 2) % 8 = 1 := by 
    have h3 : (a ^ 2 + (b : ℤ) ^ 2) % 8 = (a ^ 2 % 8 + ((b : ℤ) ^ 2 % 8)) % 8 := by 
      simp [Int.add_emod]
    rw [h3, ha, hb]
    norm_num
  norm_cast at h2