import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by 
  have h1 : (a - 1) ^ 2 ≥ 0:= by 
    exact sq_nonneg (a - 1)
  linarith [sq_nonneg (a - 1)]