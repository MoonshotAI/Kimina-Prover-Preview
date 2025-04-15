import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_175 : 2 ^ 2010 % 10 = 4 := by 
  norm_num