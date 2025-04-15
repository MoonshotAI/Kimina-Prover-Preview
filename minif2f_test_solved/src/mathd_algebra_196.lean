import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    (∑ k in S, k) = 4 := by 
  have h1 : S = {-1, 5} := by
    ext x
    simp [h₀]
    constructor
    · -- |2 - x| = 3 → x ∈ {-1, 5}
      intro h
      cases eq_or_eq_neg_of_abs_eq h with
      | inl h1 =>
        left
        linarith
      | inr h2 =>
        right
        linarith
    · -- x ∈ {-1, 5} → |2 - x| = 3
      rintro (h | h)
      · -- x = -1
        rw [h]
        norm_num
      · -- x = 5
        rw [h]
        norm_num
  rw [h1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]