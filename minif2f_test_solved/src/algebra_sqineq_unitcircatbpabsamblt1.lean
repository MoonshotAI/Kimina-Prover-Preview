import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + abs (a - b) ≤ 1 := by 
  by_cases h : a - b ≥ 0 
  · -- Case 1: a - b ≥ 0, i.e., |a - b| = a - b
    rw [abs_of_nonneg h]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a - b), sq_nonneg (a + b), h₀]
  · -- Case 2: a - b < 0, i.e., |a - b| = b - a
    rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b), h₀]