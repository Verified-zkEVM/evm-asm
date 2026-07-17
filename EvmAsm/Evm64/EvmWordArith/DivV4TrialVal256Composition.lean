/-
  EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition

  Composes the `DivKTrialCallV4QHatLeFloorPlusOne` Knuth-A `+1` bound on
  `divKTrialCallV4QHat` (bead `7.1.4.1`) with the standard val256-level
  Knuth Theorem A bound (named `Knuth128_64TopWindowLeVal256DivPlusOne`
  here) to obtain the `+2` val256-level overestimate consumed by the
  BLT-path bridges `loopBodyN{2,3}CallAddbackCarry2NzV4_of_overestimate_c3`.

  This makes the BLT bridges' `hq_over` premise reducible to two named
  arithmetic frontiers, parallel to the MAX-path side.
-/

import EvmAsm.Evm64.EvmWordArith.DivV4TrialOverestimate
import EvmAsm.Evm64.EvmWordArith.DivAccumulate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Named frontier predicate for the standard Knuth Theorem A bound on the
    128/64 top-window quotient against the full val256-level quotient.

    Under normalisation, the 128/64 trial `floor((uHi*2^64 + uLo) / vTop)`
    overshoots the true val256 quotient by at most 1.  This is the
    'val256-level Knuth-A bridge' mentioned in bead `7.1.4.1`. -/
def Knuth128_64TopWindowLeVal256DivPlusOne
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
    val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1

/-- Composition: from the Knuth-A v4 `+1` bound and the Knuth Theorem A
    bound, derive the val256-level `+2` overestimate consumed by the
    BLT-path bridges. -/
theorem divKTrialCallV4QHat_le_val256_div_plus_two
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_v4 : DivKTrialCallV4QHatLeFloorPlusOne uHi uLo vTop)
    (h_knuth : Knuth128_64TopWindowLeVal256DivPlusOne uHi uLo vTop
      v0 v1 v2 v3 u0 u1 u2 u3) :
    (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 := by
  unfold DivKTrialCallV4QHatLeFloorPlusOne at h_v4
  unfold Knuth128_64TopWindowLeVal256DivPlusOne at h_knuth
  omega

end EvmAsm.Evm64
