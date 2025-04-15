import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha_pos, hb_pos, hc_pos, hd_pos⟩
  have h1 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a - (a + b + c + d) ≥ 0 := by
    have h1 : a ^ 2 / b + b - 2 * a ≥ 0 := by
      have h1 : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
        field_simp [hb_pos.ne.symm]
        ring
      have h2 : (a - b) ^ 2 ≥ 0 := by
        exact sq_nonneg (a - b)
      have h3 : (a - b) ^ 2 / b ≥ 0 := by
        apply div_nonneg
        · exact h2
        · linarith [hb_pos]
      linarith [h1, h3]
    have h2 : b ^ 2 / c + c - 2 * b ≥ 0 := by
      have h4 : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
        field_simp [hc_pos.ne.symm]
        ring
      have h5 : (b - c) ^ 2 ≥ 0 := by
        exact sq_nonneg (b - c)
      have h6 : (b - c) ^ 2 / c ≥ 0 := by
        apply div_nonneg
        · exact h5
        · linarith [hc_pos]
      linarith [h4, h6]
    have h3 : c ^ 2 / d + d - 2 * c ≥ 0 := by
      have h7 : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
        field_simp [hd_pos.ne.symm]
        ring
      have h8 : (c - d) ^ 2 ≥ 0 := by
        exact sq_nonneg (c - d)
      have h9 : (c - d) ^ 2 / d ≥ 0 := by
        apply div_nonneg
        · exact h8
        · linarith [hd_pos]
      linarith [h7, h9]
    have h4 : d ^ 2 / a + a - 2 * d ≥ 0 := by
      have h10 : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
        field_simp [ha_pos.ne.symm]
        ring
      have h11 : (d - a) ^ 2 ≥ 0 := by
        exact sq_nonneg (d - a)
      have h12 : (d - a) ^ 2 / a ≥ 0 := by
        apply div_nonneg
        · exact h11
        · linarith [ha_pos]
      linarith [h10, h12]
    have h5 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a - (a + b + c + d) ≥ 0 := by
      linarith [h1, h2, h3, h4]
    linarith [h5]
  linarith [h1]