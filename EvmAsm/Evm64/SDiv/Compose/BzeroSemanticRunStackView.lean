/-
  EvmAsm.Evm64.SDiv.Compose.BzeroSemanticRunStackView

  Run-stack semantic adapter for the SDIV zero-divisor dispatch path.
-/

import EvmAsm.Evm64.SDiv.Compose.BzeroSemanticStackAfterView
import EvmAsm.Evm64.SDiv.StackExecutionBridge

namespace EvmAsm.Evm64.SDiv.Compose

/-- v4 zero-divisor SDIV bzero path with the post stack named by a concrete
    successful `runSDivStack?` output. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_runStack_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend : EvmWord) (rest : List EvmWord)
    (out : EvmAsm.Evm64.SDivStackExecutionBridge.SDivStackResult)
    (h_run :
      EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?
        { stack := dividend :: (0 : EvmWord) :: rest } = some out)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: (0 : EvmWord) :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorSign := (0 : Word) >>> (63 : BitVec 6).toNat
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^ divisorSign
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
         evmStackIs (sp + 32) (out.effects.stackWords ++ out.stack)) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  have h_zero :=
    EvmAsm.Evm64.SDivStackExecutionBridge.runSDivStack?_zero_divisor dividend rest
  rw [h_zero] at h_run
  cases h_run
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      simpa only [EvmAsm.Evm64.SDivArgs.sdivResultFromArgs_zero_divisor,
        List.singleton_append] using hp)
    (saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_result_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase)

end EvmAsm.Evm64.SDiv.Compose
