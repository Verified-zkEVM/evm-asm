/-
  EvmAsm.Evm64.SDiv.Compose.StackSpecV5

  v5 SDIV top-level stack spec (C9): UNCONDITIONAL — over `sdivCodeV5`, from the
  SDIV opcode entry stack state to the sign-fixed callable-return post, using the
  B8 handoff (`..._from_handoff_spec_in_sdivCodeV5`) which bakes in M2's
  unconditional v5 DIV callable.  Mirror of the v4 CONDITIONAL witness
  `evm_sdiv_exact_callable_return_stack_spec_within` (SDiv/Spec.lean:456), but
  with no `hStack` hypothesis (discharged by M2), the input div128 scratch cell
  `(sp+3936) ↦ₘ scratchMem` in the stack pre, and the shed-x9 trailing frame
  `(regOwn .x9 ** memOwn (sp+3936))` in the post.
-/

import EvmAsm.Evm64.SDiv.V5ReturnShared
import EvmAsm.Evm64.SDiv.SpecShared

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- v5 UNCONDITIONAL SDIV stack spec: `sdivCodeV5`, opcode-entry stack state →
    sign-fixed callable-return post + shed-x9 frame + stack tail. -/
theorem evm_sdiv_exact_callable_return_stack_spec_within_v5
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
      ((saveRaDivCallCallableReturnPostNoX9 vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
       (regOwn .x9 ** memOwn (sp + signExtend12 3936))) **
       evmStackIs (sp + 64) rest) := by
  have hExact :=
    saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV5
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
      (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hbase halign
  have hExactFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (evmStackIs (sp + 64) rest) pcFree_evmStackIs hExact
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      have h_old :
          (((saveRaSignsAbsSignXorThenDivCallPre
              vRa vSavedOld sp sDividendOld sDivisorOld
              dividendMaskOld dividendValueOld dividendCarryOld
              (dividend.getLimbN 0) (dividend.getLimbN 1)
              (dividend.getLimbN 2) (dividend.getLimbN 3)
              (divisor.getLimbN 0) (divisor.getLimbN 1)
              (divisor.getLimbN 2) (divisor.getLimbN 3) **
            evmStackIs (sp + 64) rest) **
            ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
             EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
               shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
            ((sp + signExtend12 3936) ↦ₘ scratchMem)) h := by
        rw [saveRaSignsAbsSignXorThenDivCallPre_stack_pair_rest]
        xperm_hyp hp
      xperm_hyp h_old) (fun _ hp => hp) hExactFramed

end EvmAsm.Evm64.SDiv.Compose
