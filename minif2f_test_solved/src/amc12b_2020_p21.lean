import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2020_p21 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) : S.card = 6 := by
  have h1 : S = {400, 470, 2290, 2360, 2430, 2500} := by
    ext n
    simp [h₀]
    constructor
    · -- Assume n ∈ S
      intro hn
      rcases hn with ⟨hn_pos, h_eq⟩
      have h_n : (n : ℝ) > 0 := by exact_mod_cast hn_pos
      have eq1 : (n : ℝ) + 1000 = (70 : ℝ) * (Int.floor (Real.sqrt n)) := by
        have h2 : (Int.floor (Real.sqrt n) : ℝ) = (n + 1000) / 70 := by 
          field_simp
          linarith [h_eq]
        linarith
      have h2 : ∃ k : ℤ, Int.floor (Real.sqrt n) = k := by 
        refine ⟨Int.floor (Real.sqrt n), rfl⟩
      rcases h2 with ⟨k, hk⟩
      have eq2 : (n : ℝ) = (70 : ℝ) * k - (1000 : ℝ) := by 
        have h2 : (Int.floor (Real.sqrt n) : ℝ) = (n + 1000) / 70 := by 
          field_simp
          linarith [h_eq]
        rw [hk] at h2
        linarith
      have h3 : n = 70 * k - 1000 := by 
        have h4 : (n : ℝ) = (70 : ℝ) * k - (1000 : ℝ) := eq2
        have h5 : (n : ℝ) = (n : ℝ) := by rfl
        have h6 : (n : ℝ) = (n : ℝ) := by rfl
        have h7 : (70 : ℝ) * k - (1000 : ℝ) = (70 * k - 1000 : ℝ) := by ring
        rw [h7] at h4
        exact_mod_cast h4
      have h4 : k ≤ Real.sqrt n := by 
        have h_floor_le_sqrt : (k : ℝ) ≤ Real.sqrt n := by 
          rw [←hk]
          exact Int.floor_le (Real.sqrt n)
        exact h_floor_le_sqrt
      have h5 : Real.sqrt n < (k : ℝ) + 1 := by 
        have h_sqrt_lt_floor_plus_one : Real.sqrt n < (k : ℝ) + 1 := by 
          rw [←hk]
          exact Int.lt_floor_add_one (Real.sqrt n)
        exact h_sqrt_lt_floor_plus_one
      have h6 : (k : ℝ) ^ 2 ≤ (n : ℝ) := by 
        have h7 : (k : ℝ) ≥ 0 := by nlinarith [h4, Real.sqrt_nonneg n]
        have h8 : (k : ℝ) ^ 2 ≤ (Real.sqrt n) ^ 2 := by nlinarith [h4, Real.sqrt_nonneg n]
        have h9 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
        linarith
      have h7 : (n : ℝ) < ((k : ℝ) + 1) ^ 2 := by 
        have h8 : (Real.sqrt n) ^ 2 < ((k : ℝ) + 1) ^ 2 := by nlinarith [h5]
        have h9 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
        nlinarith [h9]
      rw [show (n : ℝ) = (70 : ℝ) * k - (1000 : ℝ) by exact_mod_cast eq2] at h6 h7
      have h8 : (k : ℝ) ^ 2 ≤ (70 : ℝ) * k - (1000 : ℝ) := by linarith
      have h9 : (70 : ℝ) * k - (1000 : ℝ) < ((k : ℝ) + 1) ^ 2 := by nlinarith
      have h10 : 20 ≤ (k : ℝ) := by 
        nlinarith [sq_nonneg ((k : ℝ) - 20), sq_nonneg ((k : ℝ) - 50), h8]
      have h11 : (k : ℝ) ≤ 50 := by 
        nlinarith [sq_nonneg ((k : ℝ) - 20), sq_nonneg ((k : ℝ) - 50), h8]
      have h12 : (k : ℝ) ^ 2 - (68 : ℝ) * k + (1001 : ℝ) > 0 := by 
        nlinarith [h9]
      have h13 : k = 20 ∨ k = 21 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 := by 
        have h14 : 20 ≤ k := by 
          norm_num at h10
          exact_mod_cast h10
        have h15 : k ≤ 50 := by 
          norm_num at h11
          exact_mod_cast h11
        interval_cases k <;> norm_num at h12 <;> tauto
      rcases h13 with (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case k = 20 
        have hn_eq : n = 400 := by 
          omega
        exact Or.inl hn_eq
      · -- Case k = 21 
        have hn_eq : n = 470 := by 
          omega
        exact Or.inr (Or.inl hn_eq)
      · -- Case k = 47 
        have hn_eq : n = 2290 := by 
          omega
        exact Or.inr (Or.inr (Or.inl hn_eq))
      · -- Case k = 48 
        have hn_eq : n = 2360 := by 
          omega
        exact Or.inr (Or.inr (Or.inr (Or.inl hn_eq)))
      · -- Case k = 49 
        have hn_eq : n = 2430 := by 
          omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn_eq))))
      · -- Case k = 50 
        have hn_eq : n = 2500 := by 
          omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn_eq))))
    · -- Show that if n ∈ {400, 470, 2290, 2360, 2430, 2500}, then n ∈ S
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 400
        constructor 
        · norm_num   -- 400 > 0
        · norm_num [Int.floor_eq_iff, Real.sqrt_eq_iff_sq_eq] <;> (norm_num)
      · -- n = 470
        constructor 
        · norm_num
        · norm_num [Int.floor_eq_iff, Real.sqrt_lt, Real.lt_sqrt] <;> (norm_num)
      · -- n = 2290
        constructor 
        · norm_num
        · norm_num [Int.floor_eq_iff, Real.sqrt_lt, Real.lt_sqrt] <;> (norm_num)
      · -- n = 2360
        constructor 
        · norm_num
        · norm_num [Int.floor_eq_iff, Real.sqrt_lt, Real.lt_sqrt] <;> (norm_num)
      · -- n = 2430
        constructor 
        · norm_num
        · norm_num [Int.floor_eq_iff, Real.sqrt_lt, Real.lt_sqrt] <;> (norm_num)
      · -- n = 2500
        constructor 
        · norm_num
        · norm_num [Int.floor_eq_iff, Real.sqrt_eq_iff_sq_eq] <;> (norm_num)
  rw [h1]
  simp