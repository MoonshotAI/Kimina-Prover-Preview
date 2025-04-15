import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by

  have h3_eq : d 3 = 1 := by
    have h3 := h₃ 3 (by norm_num)
    simp [h₂, h₀] at h3
    omega

  have h4_eq : d 4 = 1 := by
    have h4 := h₃ 4 (by norm_num)
    simp [h3_eq, h₁] at h4
    omega

  have h5_eq : d 5 = 2 := by
    have h5 := h₃ 5 (by norm_num)
    simp [h4_eq, h₂] at h5
    omega

  have h6_eq : d 6 = 3 := by
    have h6 := h₃ 6 (by norm_num)
    simp [h5_eq, h3_eq] at h6
    omega

  have h7_eq : d 7 = 4 := by
    have h7 := h₃ 7 (by norm_num)
    simp [h6_eq, h4_eq] at h7
    omega

  have h8_eq : d 8 = 6 := by
    have h8 := h₃ 8 (by norm_num)
    simp [h7_eq, h5_eq] at h8
    omega

  have h9_eq : d 9 = 9 := by
    have h9 := h₃ 9 (by norm_num)
    simp [h8_eq, h6_eq] at h9
    omega

  have h11 : ∀ n, n ≥ 2 → d (n + 7) % 2 = d n % 2 := by
    intro n hn
    have h11 := h₃ (n + 7) (by omega)
    rw [show n + 7 - 1 = n + 6 by omega, show n + 7 - 3 = n + 4 by omega] at h11
    have h12 := h₃ (n + 6) (by omega)
    rw [show n + 6 - 1 = n + 5 by omega, show n + 6 - 3 = n + 3 by omega] at h12
    have h13 := h₃ (n + 5) (by omega)
    rw [show n + 5 - 1 = n + 4 by omega, show n + 5 - 3 = n + 2 by omega] at h13
    have h14 := h₃ (n + 4) (by omega)
    rw [show n + 4 - 1 = n + 3 by omega, show n + 4 - 3 = n + 1 by omega] at h14
    have h15 := h₃ (n + 3) (by omega)
    rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 3 = n by omega] at h15
    have h16 := h₃ (n + 2) (by omega)
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 3 = n - 1 by omega] at h16
    have h17 := h₃ (n + 1) (by omega)
    rw [show n + 1 - 1 = n by omega, show n + 1 - 3 = n - 2 by omega] at h17
    have eq1 : d (n + 7) = d (n + 6) + d (n + 4) := by omega
    have eq2 : d (n + 6) = d (n + 5) + d (n + 3) := by omega
    have eq3 : d (n + 5) = d (n + 4) + d (n + 2) := by omega
    have eq4 : d (n + 4) = d (n + 3) + d (n + 1) := by omega
    have eq5 : d (n + 3) = d (n + 2) + d n := by omega
    have eq6 : d (n + 2) = d (n + 1) + d (n - 1) := by omega
    have eq7 : d (n + 1) = d n + d (n - 2) := by omega
    have h18 : d (n + 7) % 2 = d n % 2 := by
      omega
    exact h18

  have h2021_even : Even (d 2021) := by
    have h2021 : d 2021 % 2 = d 5 % 2 := by
      have h : ∀ k, d (5 + 7 * k) % 2 = d 5 % 2 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have n : 5 + 7 * k ≥ 2 := by omega
          have h11' := h11 (5 + 7 * k) n
          rw [show 5 + 7 * (k + 1) = (5 + 7 * k) + 7 by ring]
          rw [h11']
          exact ih
      have h288 : d 2021 % 2 = d 5 % 2 := by
        calc
          d 2021 % 2 = d (5 + 7 * 288) % 2 := by norm_num
          _ = d 5 % 2 := h 288
      exact h288
    have h5_mod2 : d 5 % 2 = 0 := by
      have : d 5 = 2 := h5_eq
      omega
    rw [Nat.even_iff]
    rw [h2021, h5_mod2]

  have h2022_odd : Odd (d 2022) := by
    have h2022 : d 2022 % 2 = d 6 % 2 := by
      have h : ∀ k, d (6 + 7 * k) % 2 = d 6 % 2 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have n : 6 + 7 * k ≥ 2 := by omega
          have h11' := h11 (6 + 7 * k) n
          rw [show 6 + 7 * (k + 1) = (6 + 7 * k) + 7 by ring]
          rw [h11']
          exact ih
      have h288 : d 2022 % 2 = d 6 % 2 := by
        calc
          d 2022 % 2 = d (6 + 7 * 288) % 2 := by norm_num
          _ = d 6 % 2 := h 288
      exact h288
    have h6_mod2 : d 6 % 2 = 1 := by
      have : d 6 = 3 := h6_eq
      omega
    rw [Nat.odd_iff]
    rw [h2022, h6_mod2]

  have h2023_even : Even (d 2023) := by
    have h2023 : d 2023 % 2 = d 7 % 2 := by
      have h : ∀ k, d (7 + 7 * k) % 2 = d 7 % 2 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have n : 7 + 7 * k ≥ 2 := by omega
          have h11' := h11 (7 + 7 * k) n
          rw [show 7 + 7 * (k + 1) = (7 + 7 * k) + 7 by ring]
          rw [h11']
          exact ih
      have h288 : d 2023 % 2 = d 7 % 2 := by
        calc
          d 2023 % 2 = d (7 + 7 * 288) % 2 := by norm_num
          _ = d 7 % 2 := h 288
      exact h288
    have h7_mod2 : d 7 % 2 = 0 := by
      have : d 7 = 4 := h7_eq
      omega
    rw [Nat.even_iff]
    rw [h2023, h7_mod2]

  exact ⟨h2021_even, h2022_odd, h2023_even⟩