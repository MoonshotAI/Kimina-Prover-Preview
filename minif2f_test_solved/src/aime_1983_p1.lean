import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by

        have hx_pos : (x : ℝ) > (1 : ℝ) := by exact_mod_cast ht.left
        have hy_pos : (y : ℝ) > (1 : ℝ) := by exact_mod_cast ht.right.left
        have hz_pos : (z : ℝ) > (1 : ℝ) := by exact_mod_cast ht.right.right

        have h31 : Real.log x ≠ 0 := by
            have h_log_x_pos : Real.log x > 0 := by
                apply Real.log_pos
                norm_num
                linarith
            linarith

        have h41 : Real.log y ≠ 0 := by
            have h_log_y_pos : Real.log y > 0 := by
                apply Real.log_pos
                norm_num
                linarith
            linarith

        have h51 : Real.log (x * y * z) ≠ 0 := by
            have h_log_x_y_z_pos : Real.log (x * y * z) > 0 := by
                have h1 : Real.log (x * y * z) = Real.log (x * y) + Real.log z := by
                    rw [Real.log_mul (by positivity) (by positivity)]
                have h2 : Real.log (x * y) = Real.log x + Real.log y := by
                    rw [Real.log_mul (by positivity) (by positivity)]
                have h3 : Real.log x > 0 := by
                    apply Real.log_pos
                    norm_num
                    linarith
                have h4 : Real.log y > 0 := by
                    apply Real.log_pos
                    norm_num
                    linarith
                have h5 : Real.log z > 0 := by
                    apply Real.log_pos
                    norm_num
                    linarith
                have h6 : Real.log (x * y) > 0 := by linarith [h3, h4]
                have h7 : Real.log (x * y * z) > 0 := by linarith [h1, h6, h5]
                linarith
            linarith

        have h3 : Real.log w = 24 * Real.log x := by
            have eq1 : Real.log w = 24 * Real.log x := by
                field_simp [h31] at h0
                linarith
            exact eq1

        have h4 : Real.log w = 40 * Real.log y := by
            have eq1 : Real.log w = 40 * Real.log y := by
                field_simp [h41] at h1
                linarith
            exact eq1

        have h5 : Real.log w = 12 * Real.log (x * y * z) := by
            have eq1 : Real.log w = 12 * Real.log (x * y * z) := by
                field_simp [h51] at h2
                linarith
            exact eq1

        have h6 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
            all_goals linarith

        rw [h6] at h5

        have h7 : Real.log z ≠ 0 := by
            have hz1 : (z : ℝ) > (1 : ℝ) := by exact_mod_cast ht.right.right
            have h_pos : Real.log z > 0 := by
                apply Real.log_pos
                norm_num
                linarith
            linarith

        have h8 : Real.log z = (2 / 3) * Real.log y := by
            have eq1 : Real.log x = (5 / 3) * Real.log y := by
                have h10 : Real.log w = 24 * Real.log x := by linarith [h3]
                have h11 : Real.log w = 40 * Real.log y := by linarith [h4]
                have h12 : 24 * Real.log x = 40 * Real.log y := by linarith [h10, h11]
                linarith

            have eq2 : Real.log x = Real.log y + Real.log z := by
                have h13 : Real.log w = 24 * Real.log x := by linarith [h3]
                have h14 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by linarith [h5]
                have h15 : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by linarith [h13, h14]
                have h16 : Real.log x = Real.log y + Real.log z := by
                    nlinarith
                exact h16

            have eq3 : Real.log z = (2 / 3) * Real.log y := by
                linarith [eq1, eq2]
            linarith

        have h9 : Real.log w / Real.log z = 60 := by
            have h21 : Real.log z ≠ 0 := by exact h7
            have h23 : Real.log w = 40 * Real.log y := by linarith [h4]
            have h24 : Real.log z = (2 / 3) * Real.log y := by linarith [h8]
            have h25 : Real.log w / Real.log z = 60 := by
                have h26 : Real.log z ≠ 0 := by exact h7
                have h27 : Real.log w = 60 * Real.log z := by
                    linarith [h23, h24]
                have h28 : Real.log w / Real.log z = 60 := by
                    field_simp [h26]
                    linarith [h27]
                exact h28
            exact h25

        exact h9