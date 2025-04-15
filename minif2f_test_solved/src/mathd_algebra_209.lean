import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
  have h1 : σ.1 10 = 2 := by 
    rw [←h₀]
    apply Equiv.right_inv
  have h2 : σ.1 2 = 1 := by 
    rw [←h₂]
    apply Equiv.right_inv
  rw [h1]
  exact h2