import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have ha : a ^ 2 + a - 1 = 0 := by linarith
  have hc : c ^ 2 + c - 1 = 0 := by linarith
  have h5 : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    rw [h₀, h₂]
    have h6 : a + c = -1 := by
      have h1 : a ^ 2 - c ^ 2 + a - c = 0 := by linarith [ha, hc]
      have h2 : (a - c) * (a + c + 1) = 0 := by 
        ring_nf at h1 ⊢
        linarith
      have h3 : a + c + 1 = 0 := by
        have h4 : a - c ≠ 0 := sub_ne_zero.mpr h₄
        apply (mul_eq_zero.mp h2).resolve_left
        exact h4
      linarith
    have h7 : (a - c) ^ 2 = 5 := by
      have h8 : (a - c) ^ 2 = (a + c) ^ 2 - 4 * (a * c) := by 
        ring
      rw [h8]
      have h9 : (a + c) ^ 2 = 1 := by 
        rw [h6]
        norm_num
      have h10 : a * c = -1 := by 
        have h11 : a ^ 2 - c ^ 2 + a - c = 0 := by linarith [ha, hc]
        have h12 : a * c = -1 := by 
          have h13 : a - c ≠ 0 := sub_ne_zero.mpr h₄
          have h14 : (a - c) * (a + c + 1) = 0 := by 
            ring_nf at h11 ⊢
            linarith
          have h15 : a + c + 1 = 0 := by 
            cases (mul_eq_zero.mp h14) with
            | inl h16 => exfalso; exact h13 (by linarith)
            | inr h17 => linarith
          nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a - 1), sq_nonneg (c - 1)]
        exact h12
      nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a - 1), sq_nonneg (c - 1)]
    nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a - 1), sq_nonneg (c - 1)]
  rw [h5]