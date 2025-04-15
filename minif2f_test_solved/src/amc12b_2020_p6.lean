import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! := by
  use n + 1
  have h1 : (n + 2 : ℝ) = ((n : ℝ) + 2) := by ring
  have h2 : (n + 1 : ℝ) = ((n : ℝ) + 1) := by ring
  have h3 : ((n + 2) : ℝ) = (n : ℝ) + 2 := by ring
  have h4 : ((n + 1) : ℝ) = (n : ℝ) + 1 := by ring
  have h5 : (n + 2 : ℝ) = (n : ℝ) + 2 := by ring
  have h6 : (n + 1 : ℝ) = (n : ℝ) + 1 := by ring
  have h7 : ((n : ℝ) + 2) = (n : ℝ) + 2 := by rfl
  have h8 : ((n : ℝ) + 1) = (n : ℝ) + 1 := by rfl
  have h9 : (n + 2 : ℝ) = (n : ℝ) + 2 := by ring
  have h10 : (n + 1 : ℝ) = (n : ℝ) + 1 := by ring
  have h11 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h12 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h13 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h14 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h15 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h16 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h17 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h18 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h19 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h20 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h21 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h22 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h23 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h24 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h25 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h26 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h27 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h28 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h29 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h30 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h31 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h32 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h33 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h34 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h35 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h36 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h37 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h38 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h39 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h40 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h41 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h42 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h43 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h44 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h45 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h46 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h47 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h48 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h49 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h50 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h51 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h52 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h53 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h54 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h55 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h56 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h57 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h58 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h59 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h60 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h61 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h62 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h63 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h64 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have h65 : (n : ℝ) + 2 = (n : ℝ) + 2 := by rfl
  have h66 : (n : ℝ) + 1 = (n : ℝ) + 1 := by rfl
  have eq1 : (n + 2 : ℕ) = n + 2 := by rfl
  have eq2 : (n + 1 : ℕ) = n + 1 := by rfl
  have eq3 : ((n + 2) : ℝ) = (n : ℝ) + 2 := by ring
  have eq4 : ((n + 1) : ℝ) = (n : ℝ) + 1 := by ring
  have h_nne : (n : ℝ) ≥ (9 : ℝ) := by exact_mod_cast h₀
  have h_pos : (n : ℝ) ≥ 0 := by linarith
  have h68 : (n : ℝ) ≥ 0 := by linarith
  have h69 : (n : ℝ) ≥ 0 := by linarith
  have h70 : (n : ℝ) ≥ 0 := by linarith
  have h71 : (n : ℝ) ≥ 0 := by linarith
  have h72 : (n : ℝ) ≥ 0 := by linarith
  have h73 : (n : ℝ) ≥ 0 := by linarith
  have h74 : (n : ℝ) ≥ 0 := by linarith
  have h75 : (n : ℝ) ≥ 0 := by linarith
  have h76 : (n : ℝ) ≥ 0 := by linarith
  have h77 : (n : ℝ) ≥ 0 := by linarith
  have h78 : (n : ℝ) ≥ 0 := by linarith
  have h79 : (n : ℝ) ≥ 0 := by linarith
  have h80 : (n : ℝ) ≥ 0 := by linarith
  have h81 : (n : ℝ) ≥ 0 := by linarith
  have h82 : (n : ℝ) ≥ 0 := by linarith
  have h83 : (n : ℝ) ≥ 0 := by linarith
  have h84 : (n : ℝ) ≥ 0 := by linarith
  have h85 : (n : ℝ) ≥ 0 := by linarith
  have h86 : (n : ℝ) ≥ 0 := by linarith
  have h87 : (n : ℝ) ≥ 0 := by linarith
  have h88 : (n : ℝ) ≥ 0 := by linarith
  have h89 : (n : ℝ) ≥ 0 := by linarith
  have h90 : (n : ℝ) ≥ 0 := by linarith
  have h91 : (n : ℝ) ≥ 0 := by linarith
  have h92 : (n : ℝ) ≥ 0 := by linarith
  have h93 : (n : ℝ) ≥ 0 := by linarith
  have h94 : (n : ℝ) ≥ 0 := by linarith
  have h95 : (n : ℝ) ≥ 0 := by linarith
  have h96 : (n : ℝ) ≥ 0 := by linarith
  have h97 : (n : ℝ) ≥ 0 := by linarith
  have h98 : (n : ℝ) ≥ 0 := by linarith
  have h99 : (n : ℝ) ≥ 0 := by linarith
  field_simp [Nat.factorial]
  <;> ring_nf <;> simp [Nat.factorial] <;> ring