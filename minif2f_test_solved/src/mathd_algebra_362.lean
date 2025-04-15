import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  have h3 : a = 27 / 4 * b ^ 3 := by
    have hb3 : b ^ 3 ≠ 0 := by
      intro h
      have : b = 0 := by
        have h1 : b ^ 3 = 0 := by linarith
        have h2 : b = 0 := by
          have h3 : b ^ 3 = 0 := by linarith
          simp at h3
          linarith
        exact h2
      contradiction
    field_simp [hb3] at h₁
    linarith
  have h4 : a ^ 2 * b ^ 3 = 32 / 27 := h₀
  rw [h3] at h4
  have h5 : (27 / 4 * b ^ 3) ^ 2 * b ^ 3 = 32 / 27 := by linarith
  have h6 : (27 / 4 * b ^ 3) ^ 2 * b ^ 3 = (729 / 16) * b ^ 9 := by
    ring_nf
  rw [h6] at h5
  have hb9 : b ^ 9 = 512 / 19683 := by
    nlinarith
  have hb : b = 2 / 3 := by
    have h8 : b ^ 9 - 512 / 19683 = 0 := by linarith [hb9]
    have h9 : (b - 2 / 3) * (b ^ 8 + (2 / 3) * b ^ 7 + (2 / 3) ^ 2 * b ^ 6 + (2 / 3) ^ 3 * b ^ 5 + (2 / 3) ^ 4 * b ^ 4 + (2 / 3) ^ 5 * b ^ 3 + (2 / 3) ^ 6 * b ^ 2 + (2 / 3) ^ 7 * b + (2 / 3) ^ 8) = 0 := by
      ring_nf
      nlinarith [h8]
    cases (mul_eq_zero.mp h9) with
    | inl h10 => 
      linarith
    | inr h11 =>
      have hb_pos : b > 0 := by
        have h9_pos : b ^ 9 > 0 := by
          rw [hb9]
          norm_num
        have : b > 0 := by
          by_contra h
          push_neg at h
          have h1 : b ≤ 0 := by linarith
          have h2 : b ^ 9 ≤ 0 := by
            nlinarith [sq_nonneg (b ^ 4), sq_nonneg (b ^ 3), sq_nonneg (b ^ 2), sq_nonneg (b)]
          linarith [h9_pos, h2]
        exact this
      have h12 : b ^ 8 + (2 / 3) * b ^ 7 + (2 / 3) ^ 2 * b ^ 6 + (2 / 3) ^ 3 * b ^ 5 + (2 / 3) ^ 4 * b ^ 4 + (2 / 3) ^ 5 * b ^ 3 + (2 / 3) ^ 6 * b ^ 2 + (2 / 3) ^ 7 * b + (2 / 3) ^ 8 > 0 := by
        nlinarith [sq_nonneg (b ^ 4), sq_nonneg (b ^ 3), sq_nonneg (b ^ 2), sq_nonneg (b), hb_pos]
      linarith [h11, h12]
  have ha : a = 2 := by
    rw [hb] at h3
    nlinarith [h3]
  rw [ha, hb]
  norm_num