import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by 
  calc
    (Complex.I / 2) ^ 2 = (Complex.I ^ 2) / (2 ^ 2) := by ring
    _ = (-1) / (2 ^ 2) := by rw [Complex.I_sq]
    _ = (-1) / 4 := by norm_num
    _ = -(1 / 4) := by ring