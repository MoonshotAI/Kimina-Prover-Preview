import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by

  rcases h₀ with ⟨hp, hq⟩
  rcases h₁ with ⟨hp_ge, hp_le⟩
  rcases h₂ with ⟨hq_ge, hq_le⟩
  interval_cases p <;> interval_cases q <;> norm_num at *
  <;> try { tauto }