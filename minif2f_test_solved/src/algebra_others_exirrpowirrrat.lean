import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2 : ℝ))
  · -- Assume $\sqrt{2}^{\sqrt{2}}$ is irrational
    use (Real.sqrt 2) ^ (Real.sqrt 2 : ℝ), Real.sqrt 2
    constructor
    · -- Show that $\sqrt{2}^{\sqrt{2}}$ is irrational (from assumption)
      exact h
    constructor
    · -- Show that $\sqrt{2}$ is irrational
      apply irrational_sqrt_two
    · -- Show that $(\sqrt{2}^{\sqrt{2}})^{\sqrt{2}}$ is rational
      have h1 : Real.sqrt 2 > (0 : ℝ) := by
        apply Real.sqrt_pos.mpr
        norm_num
      have h2 : ((Real.sqrt 2) ^ (Real.sqrt 2 : ℝ)) ^ (Real.sqrt 2 : ℝ) = (Real.sqrt 2) ^ ((Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ)) := by
        rw [Real.rpow_mul]
        all_goals linarith [h1]
      have h3 : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
        exact Real.mul_self_sqrt (by norm_num)
      rw [h2, h3]
      have h4 : (Real.sqrt 2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) := by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num]
        simp [Real.rpow_natCast, Real.sq_sqrt]
        all_goals norm_num
      rw [h4]
      norm_num
  · -- Assume $\sqrt{2}^{\sqrt{2}}$ is rational
    use Real.sqrt 2, Real.sqrt 2
    constructor
    · -- Show that $\sqrt{2}$ is irrational
      apply irrational_sqrt_two
    constructor
    · -- Show that $\sqrt{2}$ is irrational
      apply irrational_sqrt_two
    · -- Show that $\sqrt{2}^{\sqrt{2}}$ is rational
      simpa using h