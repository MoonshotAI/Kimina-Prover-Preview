import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 h₁
  | succ n ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      norm_num
      simp [pow_succ] at ih ⊢
      nlinarith [sq_nonneg (x), sq_nonneg (x + 1), ih, h₀]