import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  specialize h 2 4
  have h1 : ∃ i j : ℤ, (2 = 2 * i) ∧ (4 = 2 * j) := by
    use 1, 2
    all_goals norm_num
  have h2 : ¬∃ k : ℤ, (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 8 * k := by
    intro h3
    rcases h3 with ⟨k, hk⟩
    have : (2 : ℤ) ^ 2 + (4 : ℤ) ^ 2 = 20 := by norm_num
    rw [this] at hk
    omega
  have h3 := h.1 h1
  exact h2 h3