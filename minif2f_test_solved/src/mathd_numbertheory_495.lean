import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_495 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a % 10 = 2) (h₂ : b % 10 = 4)
    (h₃ : Nat.gcd a b = 6) : 108 ≤ Nat.lcm a b := by

  have h4 : Nat.gcd a b * Nat.lcm a b = a * b := by
    rw [Nat.gcd_mul_lcm]

  have h5 : 6 ∣ a := by
    have h6 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    rw [h₃] at h6
    exact Nat.dvd_trans (by norm_num) h6

  have h6 : 6 ∣ b := by
    have h7 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    rw [h₃] at h7
    exact Nat.dvd_trans (by norm_num) h7

  have h7 : a ≥ 12 := by
    by_contra h
    push_neg at h
    have h8 : a < 12 := h
    have h9 : a % 10 = 2 := h₁
    interval_cases a <;> norm_num at *
    all_goals omega

  have h10 : b ≥ 24 := by
    by_contra h
    push_neg at h
    have h11 : b < 24 := h
    have h12 : b % 10 = 4 := h₂
    interval_cases b <;> norm_num at *
    all_goals omega

  have h11 : 108 ≤ Nat.lcm a b := by
    by_contra h
    push_neg at h
    have h12 : Nat.lcm a b < 108 := h
    have h13 : a * b < 648 := by
      have h14 : a.gcd b * a.lcm b = a * b := by rw [Nat.gcd_mul_lcm]
      rw [h₃] at h14
      have h15 : a * b = 6 * (a.lcm b) := by linarith
      have h16 : a.lcm b < 108 := h12
      linarith [h16, h15]
    have h14 : a ≤ 54 := by nlinarith [h13, h7, h10]
    have h15 : b ≤ 54 := by nlinarith [h13, h7, h10]
    interval_cases a <;> interval_cases b
    all_goals
      norm_num at *
      all_goals
        try { contradiction }
        try { omega }
  exact h11