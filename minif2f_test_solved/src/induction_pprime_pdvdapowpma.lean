import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  have h2 : p ∣ a ^ p - a := by
    have h3 : a ^ p ≡ a [MOD p] := by
      have h4 : Fact p.Prime := ⟨h₁⟩
      have h5 : a ^ p % p = a % p := by
        have h6 : a ^ p % p = a % p := by
          have h7 : Fact p.Prime := ⟨h₁⟩
          have h8 : a ^ p % p = a % p := by
            apply (ZMod.eq_iff_modEq_nat p).mp
            have h9 : (a : ZMod p) ^ p = (a : ZMod p) := by
              rw [ZMod.pow_card]
            simp [h9]
            <;> (try { simp })
            <;> (try { omega })
          exact h8
        exact h6
      exact h5
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h3)
  exact h2