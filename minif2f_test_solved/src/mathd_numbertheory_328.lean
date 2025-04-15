import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by 
  norm_num