import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by
  have hn : n = 129199212 := by
    norm_num [h₀]
  rw [hn] at h₆
  simp [Nat.digits, Nat.digitsAux] at h₆
  have hB : B = 2 := by 
    linarith
  have hA : A = 1 := by 
    linarith
  have hC : C = 9 := by 
    linarith
  calc 
    100 * A + 10 * B + C = 100 * 1 + 10 * 2 + 9 := by rw [hA, hB, hC]
    _ = 100 + 20 + 9 := by norm_num
    _ = 129 := by norm_num