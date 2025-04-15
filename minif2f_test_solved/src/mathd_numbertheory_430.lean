import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  rcases h₀ with ⟨ha1, ha2⟩
  rcases h₁ with ⟨hb1, hb2⟩
  rcases h₂ with ⟨hc1, hc2⟩
  have h9 : c = a + b := by linarith
  rw [h9] at h₇
  have h10 : b = 3 * a := by 
    omega
  rw [h10] at h₈ 
  rw [h9] at h₈
  have ha_eq_1 : a = 1 := by
    nlinarith
  have hb_eq_3 : b = 3 := by 
    rw [ha_eq_1] at h10
    omega
  have hc_eq_4 : c = 4 := by 
    rw [ha_eq_1, hb_eq_3] at h₆
    omega
  calc
    a + b + c = 1 + 3 + 4 := by rw [ha_eq_1, hb_eq_3, hc_eq_4]
    _ = 8 := by norm_num