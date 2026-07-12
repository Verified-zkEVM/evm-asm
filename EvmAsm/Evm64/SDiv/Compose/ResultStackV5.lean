/-
  EvmAsm.Evm64.SDiv.Compose.ResultStackV5

  Clean-`evmStackIs` result-post twin of the unconditional v5 SDIV witness
  `evm_sdiv_exact_callable_return_stack_spec_within_v5`.  Reshapes that witness's
  raw callable-return post (`saveRaDivCallCallableReturnPostNoX9 …`) into the
  sign-fixed result word sitting on the EVM stack at `sp+32`, matching the public
  form of the v4 `evm_sdiv_exact_callable_return_result_stack_spec_within` — using
  exactly the same (code-agnostic) post weakenings, and carrying the shed-x9
  `(regOwn .x9 ** memOwn (sp+3936))` frame through.
-/

import EvmAsm.Evm64.SDiv.Compose.StackSpecV5
import EvmAsm.Evm64.SDiv.SpecShared

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- v5 UNCONDITIONAL SDIV clean result-stack spec: the sign-fixed quotient word on
    the stack at `sp+32`, over `sdivCodeV5`. -/
theorem evm_sdiv_exact_callable_return_result_stack_spec_within_v5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV5 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       (((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem)))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let resultWord :=
         sdivSignFixedWord resultSign
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let mask := (0 : Word) - resultSign
       let sum0 := (quotientWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (quotientWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (quotientWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (quotientWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (resultWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [saveRaDivCallCallableReturnPostNoX9_evmWordIs] at hp
      rw [saveRaDivCallCallableReturnSignFixedWordPostNoX9_unfold] at hp
      dsimp only at hp ⊢
      rw [evmStackIs_cons]
      rw [show (sp + 32 + 32 : Word) = sp + 64 by bv_addr]
      xperm_hyp hp)
    (evm_sdiv_exact_callable_return_stack_spec_within_v5
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hbase halign)

end EvmAsm.Evm64.SDiv.Compose
