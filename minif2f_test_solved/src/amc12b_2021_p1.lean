import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2021_p1 (S : Finset ℤ) (h₀ : ∀ x : ℤ, x ∈ S ↔ ↑(abs x) < 3 * Real.pi) :
    S.card = 19 := by

  have h1 : (3 * Real.pi) > 9 := by
    have hpi : Real.pi > 3 := Real.pi_gt_three
    linarith
  
  have h2 : (3 * Real.pi) < 9.45 := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_315
    norm_num at hpi ⊢
    linarith
  
  have h3 : S = Finset.Icc (-9) 9 := by
    ext x
    simp [h₀]
    constructor
    · -- If x ∈ S, then |x| < 3π
      intro hx
      have h4 : abs x < 3 * Real.pi := by exact_mod_cast hx
      have h5 : abs x ≤ 9 := by
        by_contra h
        push_neg at h
        have h6 : abs x ≥ 10 := by omega
        have h7 : (10 : ℝ) ≤ (abs x : ℝ) := by exact_mod_cast h6
        have h8 : (abs x : ℝ) < 3 * Real.pi := by exact_mod_cast h4
        linarith [h2]
      constructor
      · -- Show that -9 ≤ x
        cases' abs_cases x with hx hx
        · -- x ≥ 0, so |x| = x
          linarith [abs_nonneg x]
        · -- x < 0, so |x| = -x
          linarith [abs_nonneg x]
      · -- Show that x ≤ 9
        cases' abs_cases x with hx hx
        · -- x ≥ 0, so |x| = x
          linarith [abs_nonneg x]
        · -- x < 0, so |x| = -x
          linarith [abs_nonneg x]
    · -- If -9 ≤ x ≤ 9, then x ∈ S
      rintro ⟨h1, h2⟩
      have h3 : abs x ≤ 9 := by
        apply abs_le.mpr
        constructor <;> linarith
      have h4 : (abs x : ℝ) < 3 * Real.pi := by
        have h5 : (abs x : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h3
        linarith [h1]
      exact_mod_cast h4
  
  rw [h3]
  native_decide