import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_185 (n : ℕ) (h₀ : n % 5 = 3) : 2 * n % 5 = 1 := by 
  omega -- The omega tactic is powerful for solving arithmetic goals involving natural numbers. It can deduce that if $n \bmod 5 = 3$, then $2n \bmod 5 = 1$ directly from the properties of modular arithmetic.