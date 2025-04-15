import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem mathd_numbertheory_237 : (∑ k in Finset.range 101, k) % 6 = 4 := by 
  calc 
    (∑ k in Finset.range 101, k) % 6 = 5050 % 6 := by 
      native_decide 
    _ = 4 := by 
      norm_num