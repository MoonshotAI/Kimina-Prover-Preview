import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  by_contra h
  have h1 : x ^ 5 % 11 = 0 ∨ x ^ 5 % 11 = 1 ∨ x ^ 5 % 11 = 10 := by 
    have h1 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> ( 
      norm_num [h1, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at * 
    )
  have h2 : (y ^ 2 + 4) % 11 = 2 ∨ (y ^ 2 + 4) % 11 = 4 ∨ (y ^ 2 + 4) % 11 = 5 ∨ (y ^ 2 + 4) % 11 = 6 ∨ (y ^ 2 + 4) % 11 = 7 ∨ (y ^ 2 + 4) % 11 = 8 ∨ (y ^ 2 + 4) % 11 = 9 := by 
    have h2 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
      norm_num [h2, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at * 
    )
  -- Using omega to derive the contradiction from modular constraints
  omega