/-
  EvmAsm.Evm64.SDiv.Compose.BzeroResultSignFix

  SDIV zero-divisor path through result-sign fixup.
-/

import EvmAsm.Evm64.SDiv.Compose.BzeroCallableNamedPost
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- v4 SDIV zero-divisor path through the final result sign-fix block. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_then_resultSignFix_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    EvmAsm.Rv64.cpsTripleWithin ((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21)
      base ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPost (sp + 32) resultSign 0 0 0 0 **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_bzero_callable_named_post_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hbz
  have hFramePc :
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord).pcFree := by
    rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
      EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
      EvmAsm.Evm64.divScratchOwn_unfold]
    pcFree
  have hFix :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord)
      hFramePc
      (resultSignFix_regOwn_scratch_spec_in_sdivCodeV4
        (sp + 32) resultSign 0 0 0 0 base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h (hp : (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) h) => by
      rw [saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch hbz] at hp
      exact hp)
    hPrefix hFix

end EvmAsm.Evm64.SDiv.Compose
