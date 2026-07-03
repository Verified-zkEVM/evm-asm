/-
  EvmAsm.Evm64.SMod.Compose.ResultStackV5

  Clean-`evmStackIs` result-post twin of the unconditional v5 SMOD witness
  `evm_smod_exact_callable_return_stack_spec_within_v5`.  Reshapes that witness's
  raw `smodResultSignFixPost` result cells into the sign-fixed remainder word
  sitting on the EVM stack at `sp+32` (`evmStackIs (sp+32) [EvmWord.smod
  dividend divisor]`), matching the public form of the v4
  `evm_smod_canonical_all_case_mod_call_return_result_stack_spec_within`.

  The pre is stated over `evmStackIs sp [dividend, divisor]` (bridged to the v5
  witness's limb cells via `evmStackIs_pair`/`evmWordIs_sp{,32}_unfold`); the post
  folds the result cells via `smodResultSignFixPost_smodResultSign_word` +
  `smodResultSignFixedWord_eq_smod`.  Carries the shed-x9
  `(regOwn .x9)`/`memOwn (sp+3936)` frame through.
-/

import EvmAsm.Evm64.SMod.Compose.StackSpecV5
import EvmAsm.Evm64.SMod.Compose.ResultSignFixView
import EvmAsm.Evm64.SMod.SpecSemantic

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- v5 UNCONDITIONAL SMOD clean result-stack spec: the sign-fixed remainder word
    on the EVM stack at `sp+32`, over `smodCodeV5`. -/
theorem evm_smod_exact_callable_return_result_stack_spec_within_v5
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) (smodCodeV5 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x13 ↦ᵣ x13Old) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp [dividend, divisor]) **
       (((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCallNoX1 sp
           q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0) **
        ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem)))
      (let dividendAbsWord : EvmWord :=
         smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let modWord := EvmWord.mod dividendAbsWord divisorAbsWord
       let resultSign := smodAbsSign (dividend.getLimbN 3)
       let mask := (0 : Word) - resultSign
       let sum0 := (modWord.getLimbN 0 ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := (modWord.getLimbN 1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (modWord.getLimbN 2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (modWord.getLimbN 3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) **
         (.x13 ↦ᵣ resultSign) ** (.x10 ↦ᵣ mask) **
         (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) [EvmWord.smod dividend divisor]) **
        smodSavedRaRetFrame sp base (dividend.getLimbN 3) dividendAbsWord)) **
       memOwn (sp + signExtend12 3936)) := by
  have h := evm_smod_exact_callable_return_stack_spec_within_v5
    vRa vSavedOld sp sDividendOld x13Old sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    (dividend.getLimbN 0) (dividend.getLimbN 1) (dividend.getLimbN 2) (dividend.getLimbN 3)
    (divisor.getLimbN 0) (divisor.getLimbN 1) (divisor.getLimbN 2) (divisor.getLimbN 3)
    v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base hbase halign
  refine EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h
  · -- PRE: goal's evmStackIs pre → the v5 witness's limb-cell pre
    rw [evmStackIs_pair, evmWordIs_sp_unfold, evmWordIs_sp32_unfold] at hp
    simp only [EvmAsm.Evm64.evm_smodDividendTopLimbOff,
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff,
      EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
      EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24,
      EvmAsm.Rv64.signExtend12_32, EvmAsm.Rv64.signExtend12_40,
      EvmAsm.Rv64.signExtend12_48, EvmAsm.Rv64.signExtend12_56]
    rw [show (sp + (0 : Word)) = sp from by bv_omega]
    xperm_hyp hp
  · -- POST: the v5 witness's smodResultSignFixPost → clean evmStackIs result
    rw [smodResultSignFixPost_smodResultSign_word (sp + 32) (dividend.getLimbN 3)] at hq
    rw [smodResultSignFixedWord_eq_smod dividend divisor] at hq
    dsimp only at hq ⊢
    rw [evmStackIs_single]
    xperm_hyp hq

end EvmAsm.Evm64.SMod.Compose
