import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h4 : a + b - c > 0 := by linarith
  have h5 : b + c - a > 0 := by linarith
  have h6 : c + a - b > 0 := by linarith
  
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    h4, h5, h6, mul_nonneg (show 0 ≤ a + b - c by linarith) (sq_nonneg (a - b)),
    mul_nonneg (show 0 ≤ b + c - a by linarith) (sq_nonneg (b - c)),
    mul_nonneg (show 0 ≤ c + a - b by linarith) (sq_nonneg (c - a))]