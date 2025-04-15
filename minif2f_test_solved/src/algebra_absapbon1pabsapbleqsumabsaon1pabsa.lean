import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  have h1 : abs (a + b) ≤ abs a + abs b := by
    apply abs_add
  have h2 : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs a + abs b) := by
    have h2a : abs (a + b) ≤ abs a + abs b := by
      apply abs_add
    have h2b : 0 ≤ abs (a + b) := abs_nonneg (a + b)
    have h2c : 0 ≤ abs a + abs b := by
      apply add_nonneg
      · apply abs_nonneg a
      · apply abs_nonneg b
    have h2d : 0 ≤ (1 + abs (a + b)) := by
      linarith [abs_nonneg (a + b)]
    have h2e : 0 ≤ (1 + abs a + abs b) := by
      linarith [abs_nonneg a, abs_nonneg b]
    have h2f : abs (a + b) / (1 + abs (a + b)) ≤ (abs a + abs b) / (1 + abs a + abs b) := by
      apply (div_le_div_iff (by linarith) (by linarith)).mpr
      nlinarith [abs_nonneg (a + b), abs_nonneg a, abs_nonneg b, h2a]
    exact h2f
  have h3 : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    have h3a : 0 ≤ (1 + abs a + abs b) := by
      linarith [abs_nonneg a, abs_nonneg b]
    have h3b : 0 ≤ (1 + abs a) := by
      linarith [abs_nonneg a]
    have h3c : 0 ≤ (1 + abs b) := by
      linarith [abs_nonneg b]
    have h4 : (abs a + abs b) / (1 + abs a + abs b) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
      have h4a : abs a ≥ 0 := abs_nonneg a
      have h4b : abs b ≥ 0 := abs_nonneg b
      have h4c : 1 + abs a + abs b > 0 := by linarith [abs_nonneg a, abs_nonneg b]
      have h4d : 1 + abs a > 0 := by linarith [abs_nonneg a]
      have h4e : 1 + abs b > 0 := by linarith [abs_nonneg b]
      have h5 : abs a / (1 + abs a) + abs b / (1 + abs b) - (abs a + abs b) / (1 + abs a + abs b) ≥ 0 := by
        have h5a : abs a / (1 + abs a) + abs b / (1 + abs b) - (abs a + abs b) / (1 + abs a + abs b) = 
          (abs a * (1 + abs b) * (1 + abs a + abs b) + 
          abs b * (1 + abs a) * (1 + abs a + abs b) - 
          (abs a + abs b) * (1 + abs a) * (1 + abs b)) / 
          ((1 + abs a) * (1 + abs b) * (1 + abs a + abs b)) := by
          field_simp
          <;> ring
        rw [h5a]
        have h5b : 0 ≤ (abs a * (1 + abs b) * (1 + abs a + abs b) + 
          abs b * (1 + abs a) * (1 + abs a + abs b) - 
          (abs a + abs b) * (1 + abs a) * (1 + abs b)) := by 
          nlinarith [sq_nonneg (abs a), sq_nonneg (abs b), mul_nonneg (abs_nonneg a) (abs_nonneg b)]
        have h5c : 0 < (1 + abs a) * (1 + abs b) * (1 + abs a + abs b) := by
          apply mul_pos
          apply mul_pos
          · linarith [abs_nonneg a]
          · linarith [abs_nonneg b]
          · linarith [abs_nonneg a, abs_nonneg b]
        apply div_nonneg
        · linarith
        · nlinarith [abs_nonneg a, abs_nonneg b]
      linarith [h5]
    linarith [h4]
  linarith [h2, h3]