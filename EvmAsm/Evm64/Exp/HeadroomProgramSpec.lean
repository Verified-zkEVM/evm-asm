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

open EvmAsm.Rv64 (CodeReq Program cpsTripleWithin cpsTripleWithin_weaken
  regOwn signExtend12)

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

theorem evmExpHeadroomCanonicalAppendedMulProgram_mul_entry_byte_offset :
    4 * (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).length = 408 := by
  rw [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]

theorem evmExpHeadroomCanonicalAppendedMulProgram_mul_entry_addr (base : Word) :
    base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).length) =
      base + 408 := by
  rw [EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]
  rfl

theorem evmExpHeadroomCanonicalAppendedMulProgram_end_addr (base : Word) :
    base + BitVec.ofNat 64 (4 * evmExpHeadroomCanonicalAppendedMulProgram.length) =
      base + 664 := by
  rw [evmExpHeadroomCanonicalAppendedMulProgram_length]
  rfl

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
  rw [evmExpHeadroomCanonicalAppendedMulProgram_mul_entry_addr,
    ← EvmAsm.Evm64.mul_callable_code_eq_ofProg]

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

/-- Canonical partial EXP headroom theorem over the concrete appended program,
    with the postcondition stated in terms of the executable EXP stack runner's
    successful output. This is the concrete-program counterpart needed by the
    public opcode wrapper to connect RV64 execution to stack semantics. -/
theorem evm_exp_headroom_run_stack_program_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (out : ExpStackExecutionBridge.ExpStackResult)
    (hbase : base &&& 1 = 0)
    (h_run : ExpStackExecutionBridge.runExpStack?
        { stack := baseWord :: exponentWord :: rest } = some out) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (CodeReq.ofProg base
        EvmAsm.Evm64.Exp.Compose.evmExpHeadroomCanonicalAppendedMulProgram)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomRunStackPost evmSp out) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmExpHeadroomRunStackPost_of_visibleResultStackPost h_run hp)
    (evm_exp_headroom_visible_result_stack_program_spec_within
      evmSp base baseWord exponentWord rest hbase)

/-- Canonical partial EXP headroom theorem over the concrete appended program,
    specialized to the self-computed executable EXP stack-runner output. -/
theorem evm_exp_headroom_run_stack_self_program_spec_within
    (evmSp base : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (CodeReq.ofProg base
        EvmAsm.Evm64.Exp.Compose.evmExpHeadroomCanonicalAppendedMulProgram)
      (evmExpHeadroomPublicStackPre evmSp baseWord exponentWord rest)
      (evmExpHeadroomRunStackPost evmSp
        { effects :=
            { stackWords := [EvmWord.exp baseWord exponentWord]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs baseWord exponentWord)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs baseWord exponentWord) }
          stack := rest }) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmExpHeadroomVisibleResultStackPost_to_runStackPost_self hp)
    (evm_exp_headroom_visible_result_stack_program_spec_within
      evmSp base baseWord exponentWord rest hbase)

/-- **The public EXP stack spec** (`0x0a`), over the concrete appended headroom
    program `evm_exp_msb_saved_bit_two_mul_fixed_headroom ;; mul_callable`
    (entry `base`, exit `base + 408` = the appended `mul_callable` entry).

    Pops the top two stack words and pushes `EvmWord.exp baseWord exponentWord`:
    from `evmStackIs evmSp (baseWord :: exponentWord :: rest)` the machine
    reaches `evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)`
    with `x12 = evmSp + 32`, everything clobbered shed to the owned
    `evmExpHeadroomPublicLeftoverFrame evmSp`. Unconditional in the operands;
    the only hypothesis is the even entry base `hbase`.

    Besides the live EVM stack, the precondition names the implementation's
    working resources explicitly (all values universally quantified, so no
    real caller restriction beyond ownership):
    * the RISC-V local frame at `x2 = sp` (4 dwords `sp .. sp+24` holding the
      result accumulator);
    * 8 headroom dwords plus two scratch EVM words BELOW the live stack
      (`evmSp-128 .. evmSp-32`) — the loop's MUL operand workspace (below-sp
      scratch follows the MULMOD `.proven` precedent, `sp-160..sp-8`);
    * the caller register frame (`x9/x5/x20/x16/x19/x6/x18/x1` at arbitrary
      values, `x10/x7/x11` owned, `x0 = 0`).

    This is the `.proven`-tier registry witness for EXP; it repackages
    `evm_exp_headroom_visible_result_stack_program_spec_within` with the
    existential pre/post bundles unfolded into the ADDMOD/MULMOD-style
    explicit public form. -/
theorem evm_exp_stack_spec_within
    (evmSp base sp : Word)
    (cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      h0 h1 h2 h3 h4 h5 h6 h7 v18 vOld : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (hbase : base &&& 1 = 0) :
    cpsTripleWithin (29 + ((255 + 1) * 193) + (1 + 9)) base (base + 408)
      (CodeReq.ofProg base
        EvmAsm.Evm64.Exp.Compose.evmExpHeadroomCanonicalAppendedMulProgram)
      -- RISC-V local frame at x2 = sp (result accumulator dwords)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       -- EVM stack pointer + headroom dwords below the live stack
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7) **
       -- caller register frame
       (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
       regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
       -- scratch EVM words below the live stack
       evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
       evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
       -- the live EVM stack
       evmStackIs evmSp (baseWord :: exponentWord :: rest)))
      (((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        evmExpHeadroomPublicLeftoverFrame evmSp) := by
  refine cpsTripleWithin_weaken (fun _ hp => ?_)
    (fun _ hq => by
      rw [evmExpHeadroomVisibleResultStackPost_unfold] at hq; exact hq)
    (evm_exp_headroom_visible_result_stack_program_spec_within
      evmSp base baseWord exponentWord rest hbase)
  rw [evmExpHeadroomPublicStackPre_unfold]
  refine ⟨sp, ?_⟩
  rw [evmExpHeadroomExistentialPre_unfold]
  exact ⟨⟨cOld, tOld, c6Old, c16Old, c19Old, m0, m1, m2, m3, v6,
          h0, h1, h2, h3, h4, h5, h6, h7, v18, vOld, dWord, eWord⟩,
    by rw [evmExpHeadroomPre_unfold]; exact hp⟩

end EvmAsm.Evm64
