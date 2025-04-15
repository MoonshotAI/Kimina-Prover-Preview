import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1997_p9 (a : ℝ) (h₀ : 0 < a)
    (h₁ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2)) (h₂ : 2 < a ^ 2) (h₃ : a ^ 2 < 3) :
    a ^ 12 - 144 * (1 / a) = 233 := by
  have h4 : Int.floor (a ^ 2) = 2 := by
    have h_floor : 2 ≤ a ^ 2 ∧ a ^ 2 < 3 := ⟨by nlinarith, by linarith⟩
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith

  have h5 : Int.floor (1 / a) = 0 := by
    have h6 : 1 / a < 1 := by
      have h7 : 1 < a := by nlinarith [h₂, mul_pos h₀ (show 0 < a by linarith)]
      have h8 : 1 / a < 1 := by
        rw [div_lt_iff (by linarith)]
        linarith
      linarith
    have h9 : 0 ≤ 1 / a := by 
      apply div_nonneg
      · norm_num 
      · linarith
    rw [Int.floor_eq_iff]
    constructor
    · -- Show that 0 ≤ 1/a
      linarith
    · -- Show that 1/a < 1
      linarith [h6]

  have h7 : 1 / a = a ^ 2 - 2 := by 
    rw [h5, h4] at h₁
    linarith

  have h8 : a ^ 3 - 2 * a - 1 = 0 := by 
    field_simp at h7 
    nlinarith [h₀]

  have h9 : a ^ 2 - a - 1 = 0 := by
    have h10 : a ^ 3 - 2 * a - 1 = 0 := h8
    have h11 : a ^ 2 - a - 1 = 0 := by
      have h12 : (a + 1) * (a ^ 2 - a - 1) = 0 := by 
        ring_nf at h10 ⊢
        linarith
      cases' (mul_eq_zero.mp h12) with h13 h14
      · -- Case a + 1 = 0, but a > 0, contradiction
        nlinarith
      · -- Case a^2 - a - 1 = 0, which is our goal
        linarith
    exact h11

  have ha2 : a ^ 2 = a + 1 := by linarith

  have ha3 : a ^ 3 = 2 * a + 1 := by 
    calc
      a ^ 3 = a ^ 2 * a := by ring
      _ = (a + 1) * a := by rw [ha2]
      _ = a ^ 2 + a := by ring
      _ = (a + 1) + a := by rw [ha2]
      _ = 2 * a + 1 := by ring

  have ha4 : a ^ 4 = 3 * a + 2 := by 
    calc 
      a ^ 4 = a ^ 3 * a := by ring
      _ = (2 * a + 1) * a := by rw [ha3]
      _ = 2 * a ^ 2 + a := by ring
      _ = 2 * (a + 1) + a := by rw [ha2]
      _ = 3 * a + 2 := by ring

  have ha5 : a ^ 5 = 5 * a + 3 := by 
    calc 
      a ^ 5 = a ^ 4 * a := by ring
      _ = (3 * a + 2) * a := by rw [ha4]
      _ = 3 * a ^ 2 + 2 * a := by ring
      _ = 3 * (a + 1) + 2 * a := by rw [ha2]
      _ = 5 * a + 3 := by ring

  have ha6 : a ^ 6 = 8 * a + 5 := by 
    calc 
      a ^ 6 = a ^ 5 * a := by ring
      _ = (5 * a + 3) * a := by rw [ha5]
      _ = 5 * a ^ 2 + 3 * a := by ring
      _ = 5 * (a + 1) + 3 * a := by rw [ha2]
      _ = 8 * a + 5 := by ring

  have ha7 : a ^ 7 = 13 * a + 8 := by 
    calc 
      a ^ 7 = a ^ 6 * a := by ring
      _ = (8 * a + 5) * a := by rw [ha6]
      _ = 8 * a ^ 2 + 5 * a := by ring
      _ = 8 * (a + 1) + 5 * a := by rw [ha2]
      _ = 13 * a + 8 := by ring

  have ha8 : a ^ 8 = 21 * a + 13 := by 
    calc 
      a ^ 8 = a ^ 7 * a := by ring
      _ = (13 * a + 8) * a := by rw [ha7]
      _ = 13 * a ^ 2 + 8 * a := by ring
      _ = 13 * (a + 1) + 8 * a := by rw [ha2]
      _ = 21 * a + 13 := by ring

  have ha9 : a ^ 9 = 34 * a + 21 := by 
    calc 
      a ^ 9 = a ^ 8 * a := by ring
      _ = (21 * a + 13) * a := by rw [ha8]
      _ = 21 * a ^ 2 + 13 * a := by ring
      _ = 21 * (a + 1) + 13 * a := by rw [ha2]
      _ = 34 * a + 21 := by ring

  have ha10 : a ^ 10 = 55 * a + 34 := by 
    calc 
      a ^ 10 = a ^ 9 * a := by ring
      _ = (34 * a + 21) * a := by rw [ha9]
      _ = 34 * a ^ 2 + 21 * a := by ring
      _ = 34 * (a + 1) + 21 * a := by rw [ha2]
      _ = 55 * a + 34 := by ring

  have ha11 : a ^ 11 = 89 * a + 55 := by 
    calc 
      a ^ 11 = a ^ 10 * a := by ring
      _ = (55 * a + 34) * a := by rw [ha10]
      _ = 55 * a ^ 2 + 34 * a := by ring
      _ = 55 * (a + 1) + 34 * a := by rw [ha2]
      _ = 89 * a + 55 := by ring

  have ha12 : a ^ 12 = 144 * a + 89 := by 
    calc 
      a ^ 12 = a ^ 11 * a := by ring
      _ = (89 * a + 55) * a := by rw [ha11]
      _ = 89 * a ^ 2 + 55 * a := by ring
      _ = 89 * (a + 1) + 55 * a := by rw [ha2]
      _ = 144 * a + 89 := by ring

  have h10 : 1 / a = a - 1 := by 
    have h11 : a ^ 2 = a + 1 := ha2
    have h12 : 1 / a = a - 1 := by 
      field_simp at h7 ⊢
      nlinarith
    linarith

  rw [ha12, h10]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]