import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h₃ : a ≥ 0 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
              mul_self_nonneg (a + b + c - 2), mul_self_nonneg (a * b + b * c + c * a - 1),
              h₀.left, h₀.right]
  have h₄ : a ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
              mul_self_nonneg (a + b + c - 2), mul_self_nonneg (a * b + b * c + c * a - 1),
              h₀.left, h₀.right]
  have h₅ : 1 / 3 ≤ b := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
              mul_self_nonneg (a + b + c - 2), mul_self_nonneg (a * b + b * c + c * a - 1),
              h₀.left, h₀.right]
  have h₆ : b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
              mul_self_nonneg (a + b + c - 2), mul_self_nonneg (a * b + b * c + c * a - 1),
              h₀.left, h₀.right]
  have h₇ : 1 ≤ c := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
              mul_self_nonneg (a + b + c - 2), mul_self_nonneg (a * b + b * c + c * a - 1),
              h₀.left, h₀.right]
  have h₈ : c ≤ 4 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1), sq_nonneg (c - 4 / 3),
              mul_self_nonneg (a + b + c - 2), mul_self_nonneg (a * b + b * c + c * a - 1),
              h₀.left, h₀.right]
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩