import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_618 (n : ℕ) (hn : n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by
  have h2 : p n = n ^ 2 - n + 41 := h₀ n
  have h3 : p (n + 1) = (n + 1) ^ 2 - (n + 1) + 41 := h₀ (n + 1)
  rw [h2, h3] at h₁
  by_contra h
  push_neg at h
  interval_cases n <;> norm_num [h₀] at h₁ <;> contradiction