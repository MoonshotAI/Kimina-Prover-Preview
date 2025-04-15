import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_457 (n : ℕ) (h₀ : 0 < n) (h₁ : 80325 ∣ n !) : 17 ≤ n := by
  by_contra h
  push_neg at h
  have h2 : n ≤ 16 := by linarith
  interval_cases n <;> contradiction