import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_559 (x y : ℕ) (h₀ : x % 3 = 2) (h₁ : y % 5 = 4) (h₂ : x % 10 = y % 10) :
    14 ≤ x := by
  have hy1 : y % 10 = 4 ∨ y % 10 = 9 := by
    have h4 : y % 5 = 4 := h₁
    omega
  rcases hy1 with hy1 | hy1
  · -- Case 1: y % 10 = 4
    have hx1 : x % 10 = 4 := by omega
    omega
  · -- Case 2: y % 10 = 9
    have hx1 : x % 10 = 9 := by omega
    omega