import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have h1 : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  have h2 : (60 * x : ℝ) * (12 * x) * (63 * x) = (36 * x) ^ 2 * (35 * x) := by
    ring_nf
  rw [h1]
  rw [h2]
  have h3 : Real.sqrt ((36 * x) ^ 2 * (35 * x)) = Real.sqrt ((36 * x) ^ 2) * Real.sqrt (35 * x) := by
    rw [Real.sqrt_mul (by positivity)]
  rw [h3]
  have h4 : Real.sqrt ((36 * x) ^ 2) = 36 * x := by
    rw [Real.sqrt_sq (by positivity)]
  rw [h4]
  all_goals positivity