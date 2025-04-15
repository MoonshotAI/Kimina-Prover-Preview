import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem amc12_2000_p12 (a m c : ℕ) (h₀ : a + m + c = 12) :
    a * m * c + a * m + m * c + a * c ≤ 112 := by 
  have h1 : a ≤ 12 := by omega
  have h2 : m ≤ 12 := by omega
  have h3 : c ≤ 12 := by omega

  interval_cases a <;> interval_cases m <;> omega