/-
  EvmAsm.Evm64.SDiv.Compose.DivCallReturnHandoffV5

  v5 SDIV B8: feed the concrete step-2 dispatch-ready handoff
  (`saveRaDivCallDispatchReadyPost_x9owned_divCode_framed_spec_in_sdivCodeV5`)
  into the B7 return chain, landing `saveRaDivCallCallableReturnPostNoX9` (+ the
  trailing `regOwn .x9 ** memOwn (sp+3936)` frame).  Mirror of the v4
  `..._exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV4`
  (DivCallExactReturnHandoff.lean:79), but the callable is M2's UNCONDITIONAL v5
  spec (no `hStack` hypothesis), so step-2 feeds directly.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallReturnV5
import EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoffV5

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- B8: v5 SDIV wrapper prefix + exact unsigned-DIV callable (M2 feed) + result
    sign-fix + saved-RA return, from the concrete step-2 handoff, over
    `sdivCodeV5`. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV5 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
  have hExit :
      (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) =
        (vRa &&& ~~~(1 : Word)) := by
    rw [EvmAsm.Rv64.signExtend12_0]
    simp [BitVec.add_zero]
  rw [← hExit]
  have hStep2 :=
    saveRaDivCallDispatchReadyPost_x9owned_divCode_framed_spec_in_sdivCodeV5
      (F := empAssertion)
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem hbase halign
  simp only [sepConj_emp_right'] at hStep2
  exact
    saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_noX9_spec_in_sdivCodeV5
      (nSteps := EvmAsm.Evm64.unifiedDivBound + 1)
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hStep2

end EvmAsm.Evm64.SDiv.Compose
