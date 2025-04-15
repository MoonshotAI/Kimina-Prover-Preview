import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  by_cases h1 : x ≥ 1
  · -- Case 1: x ≥ 1
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h₀
    constructor
    · linarith
    · linarith
  · -- Case 2: x < 1
    by_cases h2 : 0 ≤ x
    · -- Subcase 2a: 0 ≤ x < 1
      by_cases h3 : x < 1
      · -- 0 ≤ x < 1
        rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h₀
        constructor
        · linarith 
        · linarith
      · -- x ≥ 1 in the context of x < 1? This is a contradiction
        linarith
    · -- Subcase 2b: x < 0
      by_cases h3 : x ≥ -1
      · -- -1 ≤ x < 0
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_nonneg (by linarith)] at h₀
        constructor
        · linarith 
        · linarith
      · -- Case 3: x < -1
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)] at h₀
        constructor
        · linarith 
        · linarith