import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by 
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have h2 : 21 * n + 4 = (14 * n + 3) * 1 + (7 * n + 1) := by omega
    have h3 : 14 * n + 3 = (7 * n + 1) * 2 + 1 := by omega
    rw [h2]
    rw [h3]
    <;> simp [Nat.gcd]
    <;> omega
  exact h1