import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by

        have h3 := h₀ 1
        have h4 := h₀ 2
        have h5 := h₀ 3
        have h6 := h₀ 4
        have h7 := h₀ 5
        have h8 := h₀ 6
        have h9 := h₀ 7
        have h10 := h₀ 8
  
        have eq3 : a 3 = 2 * a 2 - a 1 := by
            linarith

        have eq4 : a 4 = 2 * a 3 - a 2 := by
            linarith

        have eq4' : a 4 = 3 * a 2 - 2 * a 1 := by
            rw [eq4, eq3]
            linarith
  
        have eq5 : a 5 = 2 * a 4 - a 3 := by 
            linarith
  
        have eq5' : a 5 = 4 * a 2 - 3 * a 1 := by
            rw [eq5, eq4', eq3]
            linarith
  
        have eq6 : a 6 = 2 * a 5 - a 4 := by 
            linarith
  
        have eq6' : a 6 = 5 * a 2 - 4 * a 1 := by
            rw [eq6, eq5', eq4']
            linarith
  
        have eq7 : a 7 = 2 * a 6 - a 5 := by 
            linarith
  
        have eq7' : a 7 = 6 * a 2 - 5 * a 1 := by
            rw [eq7, eq6', eq5']
            linarith
  
        have eq8 : a 8 = 2 * a 7 - a 6 := by 
            linarith
  
        have eq8' : a 8 = 7 * a 2 - 6 * a 1 := by
            rw [eq8, eq7', eq6']
            linarith
  
        have eq9 : a 9 = 2 * a 8 - a 7 := by 
            linarith
  
        have eq9' : a 9 = 8 * a 2 - 7 * a 1 := by
            rw [eq9, eq8', eq7']
            linarith

        have eq2 : a 2 = 41 / 60 := by 
            have h9_eq : a 9 = 8 * a 2 - 7 * a 1 := eq9'
            rw [h₁] at h9_eq
            rw [h₂] at h9_eq 
            linarith
  
        have eq5'' : a 5 = 11 / 15 := by 
            rw [eq5']
            rw [h₁, eq2]
            norm_num
  
        exact eq5''