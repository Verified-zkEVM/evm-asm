/-
  EvmAsm.Evm64.SMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_smod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  GH #90 (beads slice evm-asm-kyp6). This file now exposes the first
  caller-facing stack assertion for the v4 SMOD path: the wrapper entry
  through the signed-operand normalization prefix and into the appended
  unsigned MOD callable. The final all-case `evm_smod_stack_spec_within`
  is composed in a later slice from the remaining MOD-call return bridge
  and semantic handler facts.
-/

import EvmAsm.Evm64.SMod.Compose.Base
import EvmAsm.Evm64.SMod.SpecSemantic
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose
open EvmAsm.Rv64.Tactics

/-- Stack-level SMOD v4 prefix bridge from the public two-word EVM stack
    assertion to the named unsigned-MOD dispatch-ready post.

    This is not the final all-case `evm_smod_stack_spec_within`: it covers
    the wrapper prefix through signed absolute-value normalization and the
    `JAL` into the appended `evm_mod_callable_v4` body. The callable body and
    return/result-sign-fix suffix stay as explicit follow-up obligations. -/
theorem evm_smod_prefix_mod_call_dispatch_ready_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff)
      (smodCodeV4 base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (.x13 ↦ᵣ x13Old) **
          (.x9 ↦ᵣ sDivisorOld) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ dividendMaskOld) ** (.x7 ↦ᵣ dividendValueOld) **
          (.x11 ↦ᵣ dividendCarryOld))) **
        evmStackIs sp [dividend, divisor]) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          EvmAsm.Evm64.divScratchValuesCallNoX1 sp
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [evmStackIs_pair, evmWordIs,
        EvmAsm.Evm64.evm_smodDividendTopLimbOff,
        EvmAsm.Evm64.evm_smodDivisorTopLimbOff,
        EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
        EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24,
        EvmAsm.Rv64.signExtend12_32, EvmAsm.Rv64.signExtend12_40,
        EvmAsm.Rv64.signExtend12_48, EvmAsm.Rv64.signExtend12_56] at hp ⊢
      rw [show (sp + 0 : Word) = sp by bv_omega]
      rw [spAddr32_8, spAddr32_16, spAddr32_24] at hp
      xperm_hyp hp)
    (fun _ hp => hp)
    (saveRa_signs_abs_then_modCall_dispatchReady_spec_in_smodCodeV4
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
      (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base)

/-- Canonical production-code spelling of
    `evm_smod_prefix_mod_call_dispatch_ready_stack_spec_within`. -/
theorem evm_smod_canonical_prefix_mod_call_dispatch_ready_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff)
      (smodCodeCanonical base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (.x13 ↦ᵣ x13Old) **
          (.x9 ↦ᵣ sDivisorOld) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ dividendMaskOld) ** (.x7 ↦ᵣ dividendValueOld) **
          (.x11 ↦ᵣ dividendCarryOld))) **
        evmStackIs sp [dividend, divisor]) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          EvmAsm.Evm64.divScratchValuesCallNoX1 sp
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  simpa [smodCodeCanonical] using
    evm_smod_prefix_mod_call_dispatch_ready_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base

/-- Stack-level SMOD v4 bridge from the public two-word EVM stack assertion
    through the wrapper prefix, unsigned-MOD callable, result-sign fix, and
    saved-RA return.

    The unsigned-MOD callable proof remains an explicit parameter. This keeps
    the public SMOD spec surface free of branch-certificate case types while
    still exposing the full wrapper return path for callers that can supply the
    current no-NOP MOD callable theorem. -/
theorem evm_smod_mod_call_return_stack_spec_within
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
      base (vRa &&& ~~~(1 : Word)) (smodCodeV4 base)
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
  -- Frame scratchMem cell around the prefix triple (prefix doesn't touch sp+3936)
  have hPrefixFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      ((sp + EvmAsm.Rv64.signExtend12 (3936 : BitVec 12)) ↦ₘ scratchMem) (by pcFree)
      (evm_smod_prefix_mod_call_dispatch_ready_stack_spec_within
        vRa vSavedOld sp sDividendOld x13Old sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 base)
  -- hPrefixFramed: prefix_pre ** (sp+3936↦scratchMem) → dispatch_ready_post ** (sp+3936↦scratchMem)
  -- The seq_perm bridges: (overall_pre → hPrefixFramed.pre) via AC-perm of atoms,
  -- then (dispatch_ready_post ** scratchCell → normalized.pre) via AC-perm.
  exact EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp)
    (EvmAsm.Rv64.cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => hp)
      hPrefixFramed)
    (saveRaAbsThenModCall_then_return_named_post_normalized_from_noNop_spec_in_smodCodeV4
      vRa sp base
      (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
      (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem h_base h_stack)

/-- Canonical production-code spelling of
    `evm_smod_mod_call_return_stack_spec_within`. -/
theorem evm_smod_canonical_mod_call_return_stack_spec_within
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
  simpa [smodCodeCanonical] using
    evm_smod_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base h_base h_stack

/-- Canonical SMOD v4 return bridge with the internal sign-fixed result folded
    into the caller-visible stack word.  The unsigned-MOD callable proof remains
    an explicit parameter, matching `evm_smod_canonical_mod_call_return_stack_spec_within`. -/
theorem evm_smod_canonical_mod_call_return_result_stack_spec_within
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
    (evm_smod_canonical_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem base h_base h_stack)

-- The public all-case `evm_smod_stack_spec_within` is exported from
-- `EvmAsm.Evm64.SMod.SpecAllCase`.

end EvmAsm.Evm64
