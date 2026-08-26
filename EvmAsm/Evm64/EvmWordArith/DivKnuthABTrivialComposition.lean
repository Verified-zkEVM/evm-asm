/-
  EvmAsm.Evm64.EvmWordArith.DivKnuthABTrivialComposition

  End-to-end trivial discharge of the val256-level `+2` overestimate
  consumed by the BLT-path bridges
  (`loopBodyN{2,3}CallAddbackCarry2NzV4_of_overestimate_c3`) when BOTH
  trivial side-conditions hold simultaneously:

    * the v4 call-trial `divKTrialCallV4QHat` equals the true 128/64
      floor exactly (the `DivV4TrialFromExactQuotient` discharge),
    * the val256-level dividend/divisor equal their 128/64 window
      exactly (the `DivKnuthAEqualWindow` discharge of Knuth Theorem A).

  Composes the two trivial discharges (PRs #7045, #7046) with the
  `divKTrialCallV4QHat_le_val256_div_plus_two` composition lemma.

  This is the simplest concrete +2 bound on the BLT-path side; the
  general (non-trivial) discharge of either component remains the open
  Knuth-A v4 / Knuth Theorem A frontier (bead `7.1.4.1` and adjacent).
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivV4TrialFromExactQuotient
public import EvmAsm.Evm64.EvmWordArith.DivKnuthAEqualWindow

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `divKTrialCallV4QHat ≤ val256(u)/val256(v) + 2` under the trivial
    "exact quotient ∧ equal window" side-conditions. -/
theorem divKTrialCallV4QHat_le_val256_div_plus_two_of_exact_and_eq_window
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_exact : (divKTrialCallV4QHat uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat)
    (h_v_eq : val256 v0 v1 v2 v3 = vTop.toNat)
    (h_u_eq : val256 u0 u1 u2 u3 = uHi.toNat * 2^64 + uLo.toNat) :
    (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 :=
  divKTrialCallV4QHat_le_val256_div_plus_two uHi uLo vTop
    v0 v1 v2 v3 u0 u1 u2 u3
    (DivKTrialCallV4QHatLeFloorPlusOne_of_exact uHi uLo vTop h_exact)
    (Knuth128_64TopWindowLeVal256DivPlusOne_of_eq_window
      uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 h_v_eq h_u_eq)

end EvmAsm.Evm64
