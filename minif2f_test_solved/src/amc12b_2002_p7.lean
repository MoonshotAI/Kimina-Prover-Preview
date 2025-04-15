import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
        have hb : b = a + 1 := h₁
        have hc : c = a + 2 := by omega
        rw [hb, hc] at h₃
        have h4 : a = 4 := by
            have h_pos : 0 < a := h₀.left
            have : a ≤ 6 := by
                nlinarith [h₃, mul_pos h_pos (show 0 < a + 1 by omega), mul_pos h_pos (show 0 < a + 2 by omega),
                    show 0 < a + 1 by omega, show 0 < a + 2 by omega]
            interval_cases a <;> omega
        have ha : a = 4 := h4
        have hb' : b = 5 := by omega
        have hc' : c = 6 := by omega
        rw [ha, hb', hc']
        norm_num