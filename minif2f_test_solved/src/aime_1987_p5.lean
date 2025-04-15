import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
        have h1 : 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517 - y^2 := by linarith
        have h2 : y^2 ≤ 517 := by
          nlinarith [sq_nonneg (x * y), sq_nonneg (x * y - 17), sq_nonneg (y - 17), sq_nonneg (x - 2), sq_nonneg (x + 2)]
        have h3 : y ≤ 22 := by nlinarith [h2]
        have h4 : y ≥ -22 := by nlinarith [sq_nonneg (y + 22), sq_nonneg (y + 21), sq_nonneg (y + 20), sq_nonneg (y + 19), sq_nonneg (y + 18), sq_nonneg (y + 17), sq_nonneg (y + 16), sq_nonneg (y + 15), sq_nonneg (y + 14), sq_nonneg (y + 13), sq_nonneg (y + 12), sq_nonneg (y + 11), sq_nonneg (y + 10), sq_nonneg (y + 9), sq_nonneg (y + 8), sq_nonneg (y + 7), sq_nonneg (y + 6), sq_nonneg (y + 5), sq_nonneg (y + 4), sq_nonneg (y + 3), sq_nonneg (y + 2), sq_nonneg (y + 1), sq_nonneg (y)]
        interval_cases y <;> 
          try {
            simp_all
            <;> 
            ( 
              ring_nf 
              <;> 
              omega
            )
          }