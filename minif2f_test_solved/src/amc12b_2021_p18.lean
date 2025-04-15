import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by

  have hne : z ≠ 0 := by
    by_contra h
    rw [h] at h₀
    simp [Complex.normSq] at h₀
    all_goals linarith

  have h1 : z.re ^ 2 + z.im ^ 2 = 6 := by
    have eq1 := h₀
    simp [Complex.normSq, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at eq1
    nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im ^ 2 - 5), sq_nonneg (z.re ^ 2 + z.im ^ 2 - 6)]

  have h2 : z.re = -1 := by
    have eq1 := h₀
    simp [Complex.normSq, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at eq1
    have h_eq : (z.re + 1) ^ 2 + (z.im ^ 2 - 5) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im ^ 2 - 5), h1]
    have h_re : (z.re + 1) ^ 2 = 0 := by nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im ^ 2 - 5), h_eq]
    have h_im : (z.im ^ 2 - 5) ^ 2 = 0 := by nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.im ^ 2 - 5), h_eq]
    have h_re_zero : z.re + 1 = 0 := by nlinarith [h_re]
    linarith

  have him : z.im ^ 2 = 5 := by 
    have h_re : z.re = -1 := h2
    have h : z.re ^ 2 + z.im ^ 2 = 6 := h1
    rw [h_re] at h
    nlinarith

  have h3 : z + 6 / z = -2 := by 
    have hz_ne_zero : z ≠ 0 := hne
    have hz_re : z.re = -1 := h2
    have hz_im_sq : z.im ^ 2 = 5 := him

    have h2 : z.im = Real.sqrt 5 ∨ z.im = -Real.sqrt 5 := by
      have h3 : z.im ^ 2 - 5 = 0 := by linarith
      have h4 : z.im ^ 2 = 5 := by linarith
      have h5 : z.im = Real.sqrt 5 ∨ z.im = -Real.sqrt 5 := by 
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num
        linarith
      exact h5

    cases h2 with
    | inl him_pos =>
      have him : z.im = Real.sqrt 5 := him_pos
      have hz : z = -1 + Real.sqrt 5 * Complex.I := by 
        rw [Complex.ext_iff]
        simp [hz_re, him]
      rw [hz]
      field_simp [Complex.ext_iff, hz_re, him, mul_add, pow_two, Complex.I_mul_I]
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    
    | inr him_neg =>
      have him : z.im = -Real.sqrt 5 := him_neg
      have hz : z = -1 + (-Real.sqrt 5) * Complex.I := by 
        rw [Complex.ext_iff]
        simp [hz_re, him]
      rw [hz]
      field_simp [Complex.ext_iff, hz_re, him, mul_add, pow_two, Complex.I_mul_I]
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    
  exact h3