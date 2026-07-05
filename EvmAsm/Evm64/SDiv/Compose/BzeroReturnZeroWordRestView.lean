/-
  EvmAsm.Evm64.SDiv.Compose.BzeroReturnZeroWordRestView

  Tail-preserving zero-word view of the SDIV zero-divisor return path.
-/

import EvmAsm.Evm64.SDiv.Compose.BzeroReturnViews

namespace EvmAsm.Evm64.SDiv.Compose

/-- v4 framed variant of the SDIV zero-divisor return path that preserves the
    untouched stack tail below the two consumed operands. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_return_zero_word_rest_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       evmStackIs (sp + 64) rest)
      ((let dividendAbsWord :=
          sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        let resultSign :=
          (dividendTop >>> (63 : BitVec 6).toNat) ^^^
            (divisorTop >>> (63 : BitVec 6).toNat)
        let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
        let mask := (0 : Word) - resultSign
        let sum0 := ((0 : Word) ^^^ mask) + resultSign
        let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
        let sum1 := ((0 : Word) ^^^ mask) + carry0
        let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
        let sum2 := ((0 : Word) ^^^ mask) + carry1
        let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
        let sum3 := ((0 : Word) ^^^ mask) + carry2
        let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
        (.x18 ↦ᵣ vRa) **
        (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
          (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
          evmWordIs (sp + 32) (0 : EvmWord)) **
         saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) **
       evmStackIs (sp + 64) rest) := by
  exact EvmAsm.Rv64.cpsTripleWithin_frameR (evmStackIs (sp + 64) rest) pcFree_evmStackIs
    (saveRa_signs_abs_signXor_then_divCall_bzero_then_return_zero_word_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz)

end EvmAsm.Evm64.SDiv.Compose
