import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h1 : a ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg b, h₀]
  have h2 : b ≥ -1 := by 
    nlinarith [sq_nonneg (b + 1), sq_nonneg a, h₀]
  have h3 : (a - 1) * (b + 1) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith 
    · linarith
  have h4 : a * b + (a - b) ≤ 1 := by 
    nlinarith [h3]
  exact h4