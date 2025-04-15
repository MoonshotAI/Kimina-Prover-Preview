import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by

  have h : n ≥ 3 := h₀
  have h1 : n ! < n ^ (n - 1) := by
    cases n with
    | zero => 
      exfalso
      linarith
    | succ n => 
      cases n with
      | zero => 
        exfalso
        linarith
      | succ n => 
        cases n with
        | zero => 
          exfalso
          linarith
        | succ n => 
          cases n with
          | zero => 
            norm_num [Nat.factorial]
          | succ n => 
            have ih : (n + 3) ! < (n + 3) ^ ((n + 3) - 1) := by 
              have h2 : n + 3 ≥ 3 := by omega
              apply induction_nfactltnexpnm1ngt3
              omega
            have h3 : (n + 4) ! = (n + 4) * (n + 3) ! := by 
              rw [Nat.factorial_succ]
            have h4 : (n + 4) ^ ((n + 4) - 1) = (n + 4) ^ (n + 3) := by 
              simp [pow_succ]
            rw [h3, h4]
            have h5 : (n + 4) ^ (n + 3) = (n + 4) * (n + 4) ^ (n + 2) := by 
              ring
            rw [h5]
            have h6 : (n + 3) ! < (n + 3) ^ ((n + 3) - 1) := ih
            have h7 : (n + 3) ^ ((n + 3) - 1) = (n + 3) ^ (n + 2) := by 
              simp [pow_succ]
            rw [h7] at h6
            have h8 : (n + 3) ^ (n + 2) < (n + 4) ^ (n + 2) := by 
              apply pow_lt_pow_left
              all_goals omega
            have h9 : (n + 3) ! < (n + 4) ^ (n + 2) := by 
              linarith
            have h10 : (n + 4) * (n + 3) ! < (n + 4) * ((n + 4) ^ (n + 2)) := by 
              nlinarith [h9, show 0 < (n + 4) by omega]
            linarith
  exact h1