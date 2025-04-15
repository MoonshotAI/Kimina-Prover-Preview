import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_289 (k t m n : ℕ) (h₀ : Nat.Prime m ∧ Nat.Prime n) (h₁ : t < k)
    (h₂ : (k ^ 2 : ℤ) - m * k + n = 0) (h₃ : (t ^ 2 : ℤ) - m * t + n = 0) :
    m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
  have h4 : k + t = m := by
    have h_eq1 : (k : ℤ) ^ 2 - m * (k : ℤ) + n = 0 := by
      exact_mod_cast h₂
    have h_eq2 : (t : ℤ) ^ 2 - m * (t : ℤ) + n = 0 := by
      exact_mod_cast h₃
    have h_sub : ((k : ℤ) ^ 2 - m * (k : ℤ) + n) - ((t : ℤ) ^ 2 - m * (t : ℤ) + n) = 0 := by
      rw [h_eq1, h_eq2]
      norm_num
    have : (k : ℤ) ^ 2 - m * (k : ℤ) + n - ((t : ℤ) ^ 2 - m * (t : ℤ) + n) = 
        (k : ℤ) ^ 2 - t ^ 2 - m * ((k : ℤ) - (t : ℤ)) := by ring
    rw [this] at h_sub
    have h5 : ((k : ℤ) - (t : ℤ)) * ((k : ℤ) + (t : ℤ) - (m : ℤ)) = 0 := by
      ring_nf at h_sub ⊢
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case 1: (k : ℤ) - (t : ℤ) = 0
      have h8 : (k : ℤ) = (t : ℤ) := by linarith
      have h9 : k = t := by
        exact_mod_cast h8
      linarith [h₁, h9]
    · -- Case 2: (k : ℤ) + (t : ℤ) - (m : ℤ) = 0
      have h10 : (k : ℤ) + (t : ℤ) = (m : ℤ) := by linarith
      exact_mod_cast h10
  have h5 : k * t = n := by
    have h6 : t ≤ k := by nlinarith
    nlinarith [h4, h₂]
  have ht : t = 1 := by
    have h7 : t = 1 := by
      have h8 : t ≤ k := by nlinarith
      have h9 : t = 1 := by
        have h10 : t ∣ n := by 
          use k
          nlinarith [h5]
        have h11 : t = 1 ∨ t = n := by 
          apply (Nat.dvd_prime h₀.right).mp
          exact h10
        rcases h11 with h12 | h13
        · -- t = 1
          exact h12
        · -- t = n
          have h14 : k = 1 := by
            have h15 : k * n = n := by rw [h13] at h5; exact_mod_cast h5
            have h16 : k = 1 := by
              apply (mul_left_inj' (by linarith [Nat.Prime.two_le h₀.right] : n ≠ 0)).mp
              linarith
            exact h16
          have h17 : n < 1 := by
            nlinarith [h₁, h13, h14]
          have h18 : n ≥ 2 := Nat.Prime.two_le h₀.right
          linarith
      exact h9
    exact h7
  have hk : k = n := by
    rw [ht] at h5
    linarith
  have hn : n = 2 := by
    have h10 : m = n + 1 := by
      omega
    have h11 : n = 2 := by
      have h12 : n ≤ 2 := by
        by_contra h
        push_neg at h
        have h13 : n ≥ 3 := by omega
        have h14 : m ≥ 4 := by omega
        have h15 : ¬Nat.Prime m := by
          have h16 : m % 2 = 0 := by
            have h17 : n % 2 = 1 := by
              have h18 : n ≥ 3 := by omega
              have h19 : n ≠ 2 := by omega
              have h20 : Odd n := by
                apply Nat.Prime.odd_of_ne_two h₀.right h19
              exact Nat.odd_iff.mp h20
            omega
          have h17 : m > 2 := by omega
          apply Nat.not_prime_of_dvd_of_ne (show 2 ∣ m by omega) (by omega) (by omega)
          all_goals omega
        exact h15 h₀.left
      have h13 : n ≥ 2 := Nat.Prime.two_le h₀.right
      interval_cases n <;> tauto
    exact h11
  have h11 : m = 3 := by
    omega
  have h12 : k = 2 := by
    rw [hn] at hk
    linarith
  have h13 : t = 1 := by
    exact ht
  have h14 : m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
    rw [h11, hn, h12, h13]
    norm_num
  exact h14