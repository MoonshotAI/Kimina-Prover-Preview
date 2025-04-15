import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have h4 : 5 * b = 4 * a := by
    linarith [h₀, h₁]
  have h5 : 3 * c = 5 * b := by 
    linarith [h₁, h₂]
  have h6 : c = 4 / 3 * a := by
    have h7 : 3 * c = 5 * b := by linarith [h₁, h₂]
    have h8 : 5 * b = 4 * a := by linarith [h₀, h₁]
    linarith
  have ha : a = 1 := by 
    have h7 : 24 * a = 24 := by
      have eq1 := h₃
      have eq2 : 10 * b = 10 * (4 / 5 * a) := by 
        linarith [h4]
      have eq3 : 6 * c = 6 * (4 / 3 * a) := by 
        linarith [h6]
      rw [eq2, eq3] at eq1
      linarith
    linarith
  have hb : b = 4 / 5 := by 
    have eq1 := h4
    rw [ha] at eq1
    linarith 
  have hc : c = 4 / 3 := by 
    have eq1 := h6
    rw [ha] at eq1
    linarith 
  have hd : d = 13 / 15 := by
    have eq1 := h₀
    rw [ha, hb, hc] at eq1
    linarith
  rw [hd]
  norm_num