/-
  EvmAsm.Evm64.SMod.Compose.DividendAbsSequence

  SMOD wrapper composition through the in-place dividend absolute-value block.
-/

import EvmAsm.Evm64.SMod.Compose.DivisorSignSequence
import EvmAsm.Evm64.SMod.Compose.AbsBlockSpecs

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_then_dividendAbs_spec_in_smodCodeV4
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 27 base ((base + dividendAbsOff) + 84)
      (smodCodeV4 base)
      ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
         (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2))))
      (let sign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let mask := (0 : Word) - sign
       let xored0 := limb0 ^^^ mask
       let sum0 := xored0 + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let xored1 := limb1 ^^^ mask
       let sum1 := xored1 + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let xored2 := limb2 ^^^ mask
       let sum2 := xored2 + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let xored3 := dividendTop ^^^ mask
       let sum3 := xored3 + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (((((.x1 ↦ᵣ vRa) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x9 ↦ᵣ divisorSign) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
           divisorTop))) **
        (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           sum3)))) := by
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let xored0 := limb0 ^^^ mask
  let sum0 := xored0 + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let xored1 := limb1 ^^^ mask
  let sum1 := xored1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let xored2 := limb2 ^^^ mask
  let sum2 := xored2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let xored3 := dividendTop ^^^ mask
  let sum3 := xored3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  let extra : EvmAsm.Rv64.Assertion :=
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
      (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
     ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 6 base (base + dividendAbsOff)
      (smodCodeV4 base) pre mid := by
    -- Keep `extra` folded: the framed spec below is stated with `extra` as an
    -- opaque frame argument, and `simpa`'s closing check no longer zeta-unfolds
    -- the local definition for us.
    dsimp [pre, mid, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        extra
        (by pcFree)
        (saveRa_dividendSign_preserve_then_divisorSign_spec_in_smodCodeV4
          vRa vSavedOld sp sDividendOld x13Old dividendTop sDivisorOld divisorTop
          base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (smodCodeV4 base) absPre post := by
    have hSpec := dividendAbs_spec_in_smodCodeV4
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.condNegate256BlockPre,
      EvmAsm.Evm64.condNegate256BlockPost,
      EvmAsm.Evm64.evm_smodDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
         (.x13 ↦ᵣ (sign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
        (by pcFree)
        hSpec
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post, extra, sign, divisorSign, mask, xored0, sum0, carry0, xored1,
    sum1, carry1, xored2, sum2, carry2, xored3, sum3, carry3, mem0, mem1,
    mem2, mem3, divisorMem3] using hSeq

end EvmAsm.Evm64.SMod.Compose
