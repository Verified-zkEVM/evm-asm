/-
  EvmAsm.Evm64.SDiv.Compose.DivCallDispatchFrame

  Dispatcher scratch framing for the SDIV wrapper prefix through `divCall`.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallPrefix

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- v4 variant of `saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCode`. -/
theorem saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) := by
  have hFramePcFree :
      ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
    rw [EvmAsm.Evm64.divScratchValuesCallNoX1_unfold]
    unfold EvmAsm.Evm64.divScratchValues
    pcFree
  exact EvmAsm.Rv64.cpsTripleWithin_frameR _ hFramePcFree
    (saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)

end EvmAsm.Evm64.SDiv.Compose
