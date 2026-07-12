/-
  EvmAsm.Evm64.SMod.Compose.StackSpecV5

  v5 SMOD top-level stack spec: UNCONDITIONAL — over `smodCodeV5`, from the SMOD
  opcode-entry state to the sign-fixed callable-return post, composing the B7
  return handoff (`saveRaAbsThenModCall_then_return_of_callable_post_noX9_spec_in_smodCodeV5`)
  with the step-2 dispatch-ready handoff (which bakes in M2's unconditional v5
  MOD callable `evm_mod_callable_v5`).  No `h_stack` hypothesis (discharged by M2);
  the bzero case is handled inside `evm_mod_callable_v5`.  Mirror of the SDIV v5
  witness `evm_sdiv_exact_callable_return_stack_spec_within_v5`.
-/

import EvmAsm.Evm64.SMod.ModCallV5Shared

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- v5 UNCONDITIONAL SMOD stack spec: `smodCodeV5`, opcode-entry state →
    sign-fixed callable-return post + memOwn scratch cell.  This is the SMOD
    `.proven` witness — the B7 return handoff discharged by the step-2 handoff
    (feeding M2's unconditional v5 MOD callable). -/
theorem evm_smod_exact_callable_return_stack_spec_within_v5
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
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
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (smodCodeV5 base)
      (((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign dividendTop
       ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (smodResultSignFixPost (sp + 32) resultSign
         (modWord.getLimbN 0) (modWord.getLimbN 1)
         (modWord.getLimbN 2) (modWord.getLimbN 3) **
        smodSavedRaRetFrame sp base dividendTop dividendAbsWord)) **
       memOwn (sp + signExtend12 3936)) :=
  saveRaAbsThenModCall_then_return_of_callable_post_noX9_spec_in_smodCodeV5
    (nSteps := EvmAsm.Evm64.unifiedDivBound + 1)
    vRa vSavedOld sp sDividendOld x13Old sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
    v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base
    (saveRaAbsThenModCallDispatchReadyPost_x9owned_spec_in_smodCodeV5
      vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem hbase halign)

end EvmAsm.Evm64.SMod.Compose
