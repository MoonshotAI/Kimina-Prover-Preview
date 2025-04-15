import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have h1 : x ^ 3 % 7 = 0 ∨ x ^ 3 % 7 = 1 ∨ x ^ 3 % 7 = 6 := by
    have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> ( 
      norm_num [h1, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] 
      <;> omega
    )
  have h2 : 4 * x ^ 3 % 7 = 0 ∨ 4 * x ^ 3 % 7 = 3 ∨ 4 * x ^ 3 % 7 = 4 := by
    rcases h1 with (h1 | h1 | h1) <;> ( 
      norm_num [h1, Int.add_emod, Int.sub_emod, Int.mul_emod] 
      <;> omega
    )
  have h3 : 4 * x ^ 3 % 7 = 1 := by
    omega
  omega