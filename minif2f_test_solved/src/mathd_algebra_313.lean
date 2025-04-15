import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by 
  have h3 : i = v / z := by 
    rw [h₀]
    field_simp [Complex.ext_iff, h₂]
  rw [h3, h₁, h₂]
  field_simp [Complex.ext_iff]
  norm_num