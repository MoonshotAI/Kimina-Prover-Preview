import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem imo_1981_p6 (f : ℕ → ℕ → ℕ) (h₀ : ∀ y, f 0 y = y + 1) (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
  have h3_eq : ∀ z, f 3 z = 2 ^ (z + 3) - 3 := by
    intro z
    induction z with
    | zero =>
      have h30 : f 3 0 = 5 := by
        have h1 : f 3 0 = f 2 1 := by rw [h₁ 2]
        have h2 : f 2 1 = f 1 (f 2 0) := by rw [h₂ 1 0]
        have h3 : f 2 0 = f 1 1 := by rw [h₁ 1]
        have h4 : f 1 1 = f 0 (f 1 0) := by rw [h₂ 0 0]
        have h5 : f 1 0 = f 0 1 := by rw [h₁ 0]
        have h6 : f 0 1 = 2 := by norm_num [h₀]
        have h7 : f 0 2 = 3 := by norm_num [h₀]
        rw [h6] at h5
        rw [h5] at h4
        rw [h7] at h4
        have h8 : f 2 0 = 3 := by linarith
        rw [h8] at h2
        have h9 : f 1 3 = 5 := by
          have h11 : f 1 3 = f 0 (f 1 2) := by rw [h₂ 0 2]
          have h12 : f 1 2 = f 0 (f 1 1) := by rw [h₂ 0 1]
          have h13 : f 1 1 = 3 := by linarith
          rw [h13] at h12
          have h14 : f 0 3 = 4 := by norm_num [h₀]
          rw [h14] at h12
          have h15 : f 0 4 = 5 := by norm_num [h₀]
          rw [h12] at h11
          rw [h15] at h11
          exact h11
        rw [h9] at h2
        have h10 : f 3 0 = 5 := by linarith
        exact h10
      norm_num [h30]
    | succ z ih =>
      have eq1 : f 3 (z + 1) = f 2 (f 3 z) := by 
        rw [h₂ 2 z]
      rw [eq1]
      have h2_eq : ∀ w, f 2 w = 2 * w + 3 := by
        intro w
        induction w with
        | zero =>
          have h20 : f 2 0 = 3 := by
            have h21 : f 2 0 = f 1 1 := by rw [h₁ 1]
            have h22 : f 1 1 = 3 := by 
              have h23 : f 1 1 = f 0 (f 1 0) := by rw [h₂ 0 0]
              have h24 : f 1 0 = f 0 1 := by rw [h₁ 0]
              have h25 : f 0 1 = 2 := by norm_num [h₀]
              rw [h25] at h24
              rw [h24] at h23
              have h26 : f 0 2 = 3 := by norm_num [h₀]
              rw [h26] at h23
              linarith
            rw [h22] at h21
            linarith
          norm_num [h20]
        | succ w ih =>
          have eq1 : f 2 (w + 1) = f 1 (f 2 w) := by 
            rw [h₂ 1 w]
          rw [eq1]
          have h1_eq : ∀ z, f 1 z = z + 2 := by 
            intro z
            induction z with
            | zero =>
              have h10 : f 1 0 = 2 := by 
                have h11 : f 1 0 = f 0 1 := by rw [h₁ 0]
                have h12 : f 0 1 = 2 := by norm_num [h₀]
                rw [h12] at h11
                linarith
              norm_num [h10]
            | succ z ih =>
              have eq1 : f 1 (z + 1) = f 0 (f 1 z) := by rw [h₂ 0 z]
              rw [eq1]
              have eq2 : f 1 z = z + 2 := ih
              rw [eq2]
              have eq3 : f 0 (z + 2) = (z + 2) + 1 := by 
                rw [h₀ (z + 2)]
              rw [eq3]
              all_goals omega
          have eq2 : f 1 (f 2 w) = f 2 w + 2 := by 
            apply h1_eq 
          rw [eq2]
          have eq3 : f 2 w = 2 * w + 3 := ih
          rw [eq3]
          omega
      have eq2 : f 2 (f 3 z) = 2 * (f 3 z) + 3 := by 
        apply h2_eq 
      rw [eq2]
      have eq3 : f 3 z = 2 ^ (z + 3) - 3 := ih
      rw [eq3]
      have eq4 : 2 * (2 ^ (z + 3) - 3) + 3 = 2 ^ (z + 4) - 3 := by 
        zify
        rw [Nat.cast_sub (by 
          have h1 : 2 ^ (z + 3) ≥ 3 := by 
            have h2 : 2 ^ (z + 3) ≥ 2 ^ 3 := by 
              apply Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
            have h3 : 2 ^ 3 = 8 := by norm_num
            linarith
          omega)]
        rw [Nat.cast_sub (by 
          have h1 : 2 ^ (z + 4) ≥ 3 := by 
            have h2 : 2 ^ (z + 4) ≥ 2 ^ 3 := by 
              apply Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
            have h3 : 2 ^ 3 = 8 := by norm_num
            linarith
          omega)]
        ring
        all_goals omega
      rw [eq4]
  intro y
  have eq1 : f 4 (y + 1) = f 3 (f 4 y) := by 
    rw [h₂ 3 y]
  rw [eq1]
  have eq2 : f 3 (f 4 y) = 2 ^ (f 4 y + 3) - 3 := by 
    apply h3_eq 
  exact eq2