/-
  EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsSequence

  SDIV wrapper composition through the dividend absolute-value block.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsBlockSpec
import EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPre
import EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPost
import EvmAsm.Evm64.SDiv.Compose.BaseSignSequence

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_then_dividendAbs_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 26 base ((base + dividendAbsOff) + 84) (sdivCodeV4 base)
      (saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        divisorTop maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop)
      (saveRaSignsThenDividendAbsPost vRa sp divisorTop
        limb0 limb1 limb2 dividendTop) := by
  rw [saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold]
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
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
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
      ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 5 base (base + dividendAbsOff)
      (sdivCodeV4 base) pre mid := by
    dsimp [pre, mid, extra, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc,
      saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
        (by pcFree)
        (saveRa_dividendSign_then_divisorSign_spec_in_sdivCodeV4
          vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop
          base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (sdivCodeV4 base) absPre post := by
    have hSpec := dividendAbs_spec_in_sdivCodeV4
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    rw [dividendAbsPre_unfold, dividendAbsPost_unfold] at hSpec
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
          ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))))
        (by pcFree)
        hSpec
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose
