import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by 
  have h2 : n % 9 = 0 ∨ n % 9 = 3 ∨ n % 9 = 6 := by
    omega
  rcases h2 with (h | h | h)
  · -- n % 9 = 0
    have h1 : n % 9 = 0 := h
    omega
  · -- n % 9 = 3
    have h1 : n % 9 = 3 := h
    omega
  · -- n % 9 = 6
    have h1 : n % 9 = 6 := h
    omega