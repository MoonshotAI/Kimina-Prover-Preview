import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2009_p7 (x : ℝ) (n : ℕ) (a : ℕ → ℝ)
    (h₁ : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1)) (h₂ : a 1 = 2 * x - 3)
    (h₃ : a 2 = 5 * x - 11) (h₄ : a 3 = 3 * x + 1) (h₅ : a n = 2009) : n = 502 := by

  have h6 := h₁ 1
  simp [h₂, h₃, h₄] at h6
  have hx : x = 4 := by linarith

  have h_a1 : a 1 = 5 := by
    rw [h₂, hx]
    norm_num

  have h_a2 : a 2 = 9 := by
    rw [h₃, hx]
    norm_num

  have h_a3 : a 3 = 13 := by
    rw [h₄, hx]
    norm_num

  have seq_formula : ∀ m, a (m + 2) = 2 * a (m + 1) - a m := by
    intro m
    have h1 := h₁ m
    linarith

  have h_diff : ∀ m, a (m + 1) - a m = 4 := by
    intro m
    induction m with
    | zero =>
      have h1 := h₁ 0
      simp [h_a1, h_a2] at h1
      linarith
    | succ m ih =>
      have h1 := h₁ (m + 1)
      simp at h1 ⊢
      have h2 := h₁ m
      simp at h2
      linarith [ih, h2]

  have h_a0 : a 0 = 1 := by
    have h1 := h_diff 0
    have h2 : a 1 = 5 := by linarith [h_a1]
    simp [h2] at h1
    linarith

  have h_n : ∀ n, a n = 1 + 4 * n := by
    intro n
    induction n with
    | zero =>
      simp [h_a0]
    | succ n ih =>
      have h1 := h_diff n
      simp [ih] at h1 ⊢
      linarith

  have h_eq : a n = 1 + 4 * n := h_n n
  rw [h_eq] at h₅
  have hn : (n : ℝ) = 502 := by
    linarith
  exact_mod_cast hn