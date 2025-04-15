import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_188 (σ : Equiv ℝ ℝ) (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 := by
  have h1 : σ.1 (σ.2 2) = 2 := by 
    apply Equiv.right_inv _ 2
  have h2 : σ.1 2 = σ.2 2 := h
  calc
    σ.1 (σ.1 2) = σ.1 (σ.2 2) := by rw [h2]
    _ = 2 := by exact h1