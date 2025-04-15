import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by 
  have h1 : S = {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} := by 
    ext n
    simp [h₀]
    constructor
    · -- Assume $n \in S$, we need to prove $n \in \{-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7\}$
      intro h
      rw [abs_le] at h
      norm_num at h 
      have h1 : -3 ≤ n := by linarith 
      have h2 : n ≤ 7 := by linarith 
      have h3 : n = -3 ∨ n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by 
        omega 
      exact h3
    · -- Assume $n \in \{-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7\}$, we need to prove $n \in S$
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = -3
        norm_num [abs_le]
      · -- n = -2
        norm_num [abs_le]
      · -- n = -1
        norm_num [abs_le]
      · -- n = 0
        norm_num [abs_le]
      · -- n = 1
        norm_num [abs_le]
      · -- n = 2
        norm_num [abs_le]
      · -- n = 3
        norm_num [abs_le]
      · -- n = 4
        norm_num [abs_le]
      · -- n = 5
        norm_num [abs_le]
      · -- n = 6
        norm_num [abs_le]
      · -- n = 7
        norm_num [abs_le]
  rw [h1]
  native_decide