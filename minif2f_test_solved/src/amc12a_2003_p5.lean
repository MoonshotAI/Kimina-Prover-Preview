import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by 
  rcases h₀ with ⟨hA, hM, hC⟩
  simp [Nat.ofDigits] at h₁
  have h2 : A ≤ 9 := hA
  have h3 : M ≤ 9 := hM
  have h4 : C ≤ 9 := hC
  omega