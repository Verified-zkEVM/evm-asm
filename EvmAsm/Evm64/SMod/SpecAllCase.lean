/-
  EvmAsm.Evm64.SMod.SpecAllCase

  All-case SMOD v4 stack spec: case-splits on whether the absolute divisor is
  zero and dispatches to the bzero or nonzero wrapper as appropriate.

  GH #90 (bead evm-asm-9iqmw.9.2).
-/

import EvmAsm.Evm64.SMod.Spec
import EvmAsm.Evm64.SMod.SpecBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose

/-- All-case SMOD v4 canonical stack spec.  The unsigned-MOD callable proof for
    the nonzero divisor path remains an explicit parameter; the zero-divisor
    path is discharged internally via the v4 bzero theorem.

    Case split: if `divisor = 0` use the bzero wrapper;
                otherwise use the nonzero wrapper with the supplied `h_stack`. -/
theorem evm_smod_canonical_all_case_mod_call_return_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word) (h_base : base &&& 1 = 0)
    (h_stack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.modCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (smodAbsSign (divisor.getLimbN 3))
          ((base + modCallOff) + 4)
          v2 v5 v6
          (smodAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (smodAbsMask (divisor.getLimbN 3))
          (smodAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp
          (smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
          EvmAsm.Rv64.regOwn .x9 **
          EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)))) :
    EvmAsm.Rv64.cpsTripleWithin
      (49 + (((EvmAsm.Evm64.unifiedDivBound + 1) + 21) + 1))
      base (vRa &&& ~~~(1 : Word)) (smodCodeCanonical base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (.x13 ↦ᵣ x13Old) **
          (.x9 ↦ᵣ sDivisorOld) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ dividendMaskOld) ** (.x7 ↦ᵣ dividendValueOld) **
          (.x11 ↦ᵣ dividendCarryOld))) **
        evmStackIs sp [dividend, divisor]) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          EvmAsm.Evm64.divScratchValuesCallNoX1 sp
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem))
      (saveRaAbsThenModCallReturnPost vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))) := by
  rcases Classical.em (divisor = 0) with h_zero | h_nz
  · -- Zero divisor: use bzero spec
    exact evm_smod_canonical_bzero_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base h_base h_zero
  · -- Nonzero divisor: use canonical spec with h_stack
    exact evm_smod_canonical_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base h_base h_stack

/-- All-case SMOD v4 canonical stack spec with the final result exposed as the
    caller-visible `EvmWord.smod` stack word.  The zero-divisor path is
    discharged internally; the nonzero path remains parameterized by the
    unsigned-MOD callable proof. -/
theorem evm_smod_canonical_all_case_mod_call_return_result_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word) (h_base : base &&& 1 = 0)
    (h_stack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.modCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (smodAbsSign (divisor.getLimbN 3))
          ((base + modCallOff) + 4)
          v2 v5 v6
          (smodAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (smodAbsMask (divisor.getLimbN 3))
          (smodAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp
          (smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
          EvmAsm.Rv64.regOwn .x9 **
          EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)))) :
    EvmAsm.Rv64.cpsTripleWithin
      (49 + (((EvmAsm.Evm64.unifiedDivBound + 1) + 21) + 1))
      base (vRa &&& ~~~(1 : Word)) (smodCodeCanonical base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (.x13 ↦ᵣ x13Old) **
          (.x9 ↦ᵣ sDivisorOld) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ dividendMaskOld) ** (.x7 ↦ᵣ dividendValueOld) **
          (.x11 ↦ᵣ dividendCarryOld))) **
        evmStackIs sp [dividend, divisor]) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          EvmAsm.Evm64.divScratchValuesCallNoX1 sp
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem))
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
       EvmAsm.Rv64.memOwn (sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12))) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [saveRaAbsThenModCallReturnPost_unfold] at hp
      dsimp only at hp ⊢
      rw [smodResultSignFixedWord_eq_smod dividend divisor] at hp
      rw [evmStackIs_single]
      xperm_hyp hp)
    (evm_smod_canonical_all_case_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base h_base h_stack)

/-- Public all-case SMOD stack spec, conditional on the unsigned MOD v4 no-NOP
    stack proof used by the internal callable handoff.

    The zero-divisor path is discharged by the SMOD bzero wrapper; the nonzero
    path keeps the unsigned-MOD callable proof explicit, matching the current
    MOD coverage boundary. -/
abbrev evm_smod_stack_spec_within :=
  evm_smod_canonical_all_case_mod_call_return_result_stack_spec_within

end EvmAsm.Evm64
