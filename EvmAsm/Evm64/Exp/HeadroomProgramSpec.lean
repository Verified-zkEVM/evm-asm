/-
  Concrete-program surface for the verified headroom EXP stack theorem.

  The main EXP stack proof currently targets the canonical headroom code bundle
  expressed as a CodeReq union with appended mul_callable.  This file names
  the corresponding concrete Program and exposes the same theorem over
  CodeReq.ofProg, so the eventual public opcode wrapper can compose against a
  normal program-shaped code surface.
-/

import EvmAsm.Evm64.Exp.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (CodeReq Program cpsTripleWithin)

namespace Exp.Compose

/-- Concrete canonical headroom EXP wrapper followed by the appended
    mul_callable body used by the verified headroom stack theorem. -/
abbrev evmExpHeadroomCanonicalAppendedMulProgram : Program :=
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff ;;
  EvmAsm.Evm64.mul_callable

theorem evmExpHeadroomCanonicalAppendedMulProgram_length :
    evmExpHeadroomCanonicalAppendedMulProgram.length = 166 := by
  unfold evmExpHeadroomCanonicalAppendedMulProgram
  simp only [EvmAsm.Rv64.seq, Program.length_append,
    EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom_length,
    EvmAsm.Evm64.mul_callable_length]

theorem evmExpHeadroomCanonicalAppendedMulProgram_byte_length :
    4 * evmExpHeadroomCanonicalAppendedMulProgram.length = 664 := by
  rw [evmExpHeadroomCanonicalAppendedMulProgram_length]

/-- The canonical headroom EXP code bundle is exactly the code requirement of
    the concrete appended program. -/
theorem evmExpHeadroomCanonicalAppendedMulCode_eq_ofProg (base : Word) :
    evm_exp_headroom_canonical_appended_mul_code base =
      CodeReq.ofProg base evmExpHeadroomCanonicalAppendedMulProgram := by
  unfold evm_exp_headroom_canonical_appended_mul_code
    evm_exp_headroom_code evmExpHeadroomCanonicalAppendedMulProgram
  simp only [EvmAsm.Rv64.seq]
  symm
  have hAppend :
      CodeReq.ofProg base
          (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
              EvmAsm.Evm64.canonicalExpSquaringMulOff
              EvmAsm.Evm64.canonicalExpCondMulOff
              EvmAsm.Evm64.canonicalExpCondMulSkipOff
              EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff ++
            EvmAsm.Evm64.mul_callable) =
        (CodeReq.ofProg base
            (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
              EvmAsm.Evm64.canonicalExpSquaringMulOff
              EvmAsm.Evm64.canonicalExpCondMulOff
              EvmAsm.Evm64.canonicalExpCondMulSkipOff
              EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)).union
          (CodeReq.ofProg (base + BitVec.ofNat 64 (4 *
              (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
                EvmAsm.Evm64.canonicalExpSquaringMulOff
                EvmAsm.Evm64.canonicalExpCondMulOff
                EvmAsm.Evm64.canonicalExpCondMulSkipOff
                EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).length))
            EvmAsm.Evm64.mul_callable) := by
    exact EvmAsm.Rv64.CodeReq.ofProg_append
  rw [hAppend]
  have hOff : base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).length) =
      base + 408 := by
    rw [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]
    rfl
  rw [hOff, ← EvmAsm.Evm64.mul_callable_code_eq_ofProg]

end Exp.Compose

/-- Canonical partial EXP headroom stack specification over the concrete
    appended headroom program rather than the unfolded union code bundle. This
    is the concrete-program counterpart of `evm_exp_headroom_stack_spec_within`. -/
theorem evm_exp_headroom_stack_program_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (CodeReq.ofProg base
        EvmAsm.Evm64.Exp.Compose.evmExpHeadroomCanonicalAppendedMulProgram)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomPublicStackPost evmSp baseWord exponentWord rest) := by
  rw [← EvmAsm.Evm64.Exp.Compose.evmExpHeadroomCanonicalAppendedMulCode_eq_ofProg]
  exact evm_exp_headroom_stack_spec_within
    evmSp base baseWord exponentWord rest hbase

/-- Canonical partial EXP headroom specification over the concrete appended
    headroom program rather than the unfolded union code bundle. -/
theorem evm_exp_headroom_visible_result_stack_program_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (CodeReq.ofProg base
        EvmAsm.Evm64.Exp.Compose.evmExpHeadroomCanonicalAppendedMulProgram)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomVisibleResultStackPost evmSp baseWord exponentWord rest) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmExpHeadroomPublicStackPost_to_visibleResultStackPost hp)
    (evm_exp_headroom_stack_program_spec_within
      evmSp base baseWord exponentWord rest hbase)

end EvmAsm.Evm64
