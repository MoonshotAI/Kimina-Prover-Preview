import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  induction n with
  | zero =>
    norm_num
  | succ k ih =>
    have h1 : 4 ^ (k + 2) + 20 = 4 * (4 ^ (k + 1)) + 20 := by ring
    rw [h1]
    omega