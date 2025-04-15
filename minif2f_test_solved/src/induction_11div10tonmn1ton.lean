import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by 
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h1 : 10 ^ (n + 1) - (-1 : ℤ) ^ (n + 1) = 10 * (10 ^ n) - (-1) * (-1 : ℤ) ^ n := by 
      ring
    rw [h1]
    have h2 : 10 * (10 ^ n) - (-1) * (-1 : ℤ) ^ n = 10 * (10 ^ n - (-1 : ℤ) ^ n) + 11 * (-1 : ℤ) ^ n := by 
      ring
    rw [h2]
    omega