/-
  EvmAsm.Evm64.DivMod.Spec.N2V5DigitConservation

  Per-digit conservation for the v5 n=2 call (addback) path: a single
  `iterN2V5 true` step conserves value, `val256 in + uTop·2^256 = q·val256 v +
  val256 rem + overflow·2^256`, given the digit's carry-2 / single-borrow-c3
  conditions.  Direct application of the version-agnostic addback conservation
  core `iterWithDoubleAddback_val256_conservation_of_carry2` to the v5 trial
  `divKTrialCallV5QHat u2 u1 v1`.  Foundation for the chained
  `fullDivN2MulSubEqV5` (the n=2 conservation the loop establishes).  Bead
  `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

theorem iterN2V5_true_conservation (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult uTop
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 →
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hcarry2 :
      isAddbackCarry2Nz (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
      (iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).1.toNat * val256 v0 v1 v2 v3 +
        val256
          (iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1 +
        (iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2.toNat * 2^256 := by
  unfold iterN2V5
  simp only [if_true]
  exact iterWithDoubleAddback_val256_conservation_of_carry2
    (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hc3_one_of_borrow hcarry2

end EvmAsm.Evm64
