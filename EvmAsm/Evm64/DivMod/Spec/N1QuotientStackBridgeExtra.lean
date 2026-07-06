/-
  EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridgeExtra

  Overflow from N1QuotientStackBridge (file-size cap).
-/

import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Explicit-limb n=1 four-limb division witness from raw
    step-conservation witnesses plus the normalized final-remainder bound. -/
theorem fullDivN1_getLimbN_of_step_conservation_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hrem_lt : fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  have hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
    fullDivN1NormalizedMulSubEq_of_raw_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_zero hr2_zero hr1_zero hfinal_zero
  exact fullDivN1_getLimbN_of_limbs_normalized_mulsub_remainder_lt
    bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
    hbnz hmulsub hrem_lt


end EvmAsm.Evm64
