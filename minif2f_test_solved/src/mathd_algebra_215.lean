import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by
  have h1 : S = {8, -14} := by
    ext x
    simp [h₀]
    constructor
    · -- Assume (x + 3) ^ 2 = 121, we need to show x = 8 ∨ x = -14
      intro h
      have h_eq : (x + 3) ^ 2 = 121 := by linarith
      have h1 : x + 3 = 11 ∨ x + 3 = -11 := by
        have h2 : (x + 3) ^ 2 - 121 = 0 := by linarith
        have h3 : ((x + 3) - 11) * ((x + 3) + 11) = 0 := by
          linarith [h2]
        cases (mul_eq_zero.mp h3) with
        | inl h4 => 
          left
          linarith
        | inr h5 => 
          right
          linarith
      cases h1 with
      | inl h11 =>
        left
        linarith
      | inr h12 =>
        right
        linarith
    · -- Show that if x = 8 ∨ x = -14, then (x + 3) ^ 2 = 121
      rintro (h | h)
      · -- x = 8
        rw [h]
        norm_num
      · -- x = -14
        rw [h]
        norm_num
  rw [h1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]