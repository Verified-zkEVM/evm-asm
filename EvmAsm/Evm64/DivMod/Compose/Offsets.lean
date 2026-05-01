/-
  EvmAsm.Evm64.DivMod.Compose.Offsets

  Named constants for byte offsets of each DivMod code block from the program
  base. Canonical source of truth for `divCode`, `modCode`, `sharedDivModCode`,
  and all downstream proofs that reference block boundaries.

  Issue #301: Previously the offsets were hardcoded literals (`base + 448`,
  `base + 904`, ...) scattered across ~40 files. Adding a single instruction
  to one block would cascade into 500+ line diffs and error-prone sed-based
  replacements. Named offsets localize the knowledge to this file; the
  `drift_check_*` examples below fail at compile time if a block length
  changes without updating the corresponding offset, pointing reviewers at
  the exact constant that must be bumped.

  Layout of `divCode` / `modCode` (all values in bytes from program base):

    [phaseAOff    =   0] divK_phaseA        (32 bytes)
      [phaseABeqOff =  28]  phaseA-end BEQ → zeroPath (phaseAOff + 28)
    [phaseBOff    =  32] divK_phaseB        (84 bytes)
      [phaseBTailOff = 96]  divK_phaseB_tail sub-block (phaseBOff + 64)
    [clzOff       = 116] divK_clz           (96 bytes)
    [phaseC2Off   = 212] divK_phaseC2       (16 bytes)
    [normBOff     = 228] divK_normB         (84 bytes)
    [normAOff     = 312] divK_normA         (84 bytes)
    [copyAUOff    = 396] divK_copyAU        (36 bytes)
    [loopSetupOff = 432] divK_loopSetup     (16 bytes)
    [loopBodyOff  = 448] divK_loopBody     (460 bytes)
      [trialCallOff = 500]  divK_loopBody trial-divide call-site (loopBodyOff + 52)
      [trialMaxOff  = 504]  divK_loopBody divK_trial_max sub-block (trialCallOff + 4)
      [correctionSkipBeqOff = 728]  divK_loopBody mulsub-correction-skip BEQ entry (loopBodyOff + 280)
      [storeLoopOff = 884]  divK_store_qj sub-block (loopBodyOff + 436)
      [loopBackBgeOff = 904]  loop-back BGE entry (denormOff - 4 = loopBodyOff + 456)
    [denormOff    = 908] divK_denorm       (100 bytes)
    [epilogueOff  =1008] divK_{div,mod}_epilogue (40 bytes)
    [zeroPathOff  =1048] divK_zeroPath      (20 bytes)
    [nopOff       =1068] ADDI x0, x0, 0      (4 bytes)
    [div128Off    =1072] divK_div128       (196 bytes)
-/

import EvmAsm.Evm64.DivMod.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Block start offsets (in bytes, as Word for direct use in `base + off`)
-- ============================================================================

/-- Offset of `divK_phaseA` (the entry block). -/
abbrev phaseAOff    : Word :=    0
/-- Offset of the phaseA-end BEQ instruction inside `divK_phaseA`.
    Entry PC of the `BEQ x5, x0, 1020` instruction that branches to
    `divK_zeroPath` when the OR-reduce of the four divisor limbs equals 0
    (the b=0 detection at the end of phaseA). Sub-offset relative to the
    phaseA block (= phaseAOff + 28, i.e. 7 instructions into phaseA — the
    final branch instruction, with the next PC = `phaseBOff`). -/
abbrev phaseABeqOff : Word :=   28
/-- Offset of `divK_phaseB` (b=0 branch + leading-limb analysis). -/
abbrev phaseBOff    : Word :=   32
/-- Offset of the `divK_phaseB_tail` sub-block inside `divK_phaseB`.
    Entry PC of the leading-limb-analysis tail (16 instructions / 64 bytes
    into `divK_phaseB`); the per-limb cascade in `divK_phaseB_cascade` falls
    through to this PC, and the per-limb specs in `Compose/PhaseAB.lean`,
    `Compose/ModPhaseB.lean`, and `Compose/ModPhaseBn21.lean` invoke
    `divK_phaseB_tail_spec_within` at this address. Sub-offset relative to
    `divK_phaseB` (= phaseBOff + 64). -/
abbrev phaseBTailOff : Word :=   96
/-- Offset of `divK_clz` (count leading zeros for shift amount). -/
abbrev clzOff       : Word :=  116
/-- Offset of `divK_phaseC2` (branch on shift=0 fast path). -/
abbrev phaseC2Off   : Word :=  212
/-- Offset of `divK_normB` (normalize divisor b). -/
abbrev normBOff     : Word :=  228
/-- Offset of `divK_normA` (normalize dividend a). -/
abbrev normAOff     : Word :=  312
/-- Offset of `divK_copyAU` (copy a[] into u[] scratch). -/
abbrev copyAUOff    : Word :=  396
/-- Offset of `divK_loopSetup` (initialize loop counter j). -/
abbrev loopSetupOff : Word :=  432
/-- Offset of `divK_loopBody` (Knuth Algorithm D main loop body). -/
abbrev loopBodyOff  : Word :=  448
/-- Offset of the trial-divide call-site sub-block inside `divK_loopBody`.
    Entry PC of the BLTU/JAL sequence that loads the trial divisor and calls
    into `divK_div128`. Sub-offset relative to the loopBody block
    (= loopBodyOff + 52, i.e. 13 instructions into the loop body). -/
abbrev trialCallOff : Word :=  500
/-- Offset of the trial-quotient `divK_trial_max` sub-block inside `divK_loopBody`.
    Entry PC of the BLT-fall-through into the "max" trial-quotient `divK_trial_max`
    snippet (`q̂ = 2^64 - 1`) — the BLTU instruction at `trialCallOff` falls
    through here when the high limb does NOT equal the divisor's top limb.
    Sub-offset relative to the loopBody block (= trialCallOff + 4
    = loopBodyOff + 56, i.e. 14 instructions into the loop body). -/
abbrev trialMaxOff : Word :=  504
/-- Offset of the trial-divide JAL-to-`divK_div128` call site inside `divK_loopBody`.
    Entry PC of the BLTU-taken target / JAL instruction that calls into the
    `divK_div128` long-division subroutine to compute the trial quotient.
    Sub-offset relative to the loopBody block (= trialCallOff + 12
    = trialMaxOff + 8 = loopBodyOff + 64, i.e. 16 instructions into the loop
    body — past the trial-divide entry, immediately before the div128
    call-return PC `divCallRetOff = loopBodyOff + 68`). -/
abbrev trialJalOff : Word :=  512
/-- Offset of the `divK_mulsub_correction` sub-block inside `divK_loopBody`.
    Entry PC of the mulsub-correction snippet that computes
    `u[j..j+n] := u[j..j+n] − q̂ · v` (the trial-quotient subtract step in
    Knuth Algorithm D). Sub-offset relative to the loopBody block
    (= loopBodyOff + 88, i.e. 22 instructions into the loop body — past
    the trial-divide entry and div128 call site). -/
abbrev mulsubOff : Word :=  536
/-- Offset of the mulsub correction-skip sub-block inside `divK_loopBody`.
    Entry PC of the divK_sub_carry (sub-borrow) chain that runs along the
    skip-correction path when the trial-quotient mulsub did not borrow.
    Sub-offset relative to the loopBody block (= loopBodyOff + 176, i.e. 44
    instructions into the loop body). See docs/divmod-offset-audit.md. -/
abbrev correctionSkipOff : Word :=  624
/-- Offset of the mulsub correction-skip BEQ entry inside `divK_loopBody`.
    Entry PC of the BEQ instruction that branches over the addback correction
    block when the trial-quotient mulsub did not borrow (the "skip" path).
    Sub-offset relative to the loopBody block (= loopBodyOff + 280, i.e. 70
    instructions into the loop body). -/
abbrev correctionSkipBeqOff : Word :=  728
/-- Offset of the correction-addback sub-block entry inside `divK_loopBody`.
    Entry PC of the `divK_sub_carry` snippet that runs the carry/borrow path
    used by mulsub correction (the start of the addback-correction path,
    66 instructions into the loop body). Sub-offset relative to the loopBody
    block (= loopBodyOff + 264). -/
abbrev correctionAddbackOff : Word :=  712
/-- Offset of the add-back carry-init sub-block inside `divK_loopBody`.
    Entry PC of the `divK_addback_init` ADDI snippet that zeros the add-back
    carry register before the per-limb addback corrections (the start of the
    addback-correction body, fall-through from the correction-skip BEQ, 71
    instructions into the loop body). Sub-offset relative to the loopBody
    block (= correctionSkipBeqOff + 4 = loopBodyOff + 284). -/
abbrev addbackInitOff : Word :=  732
/-- Offset of the limb-0 addback step inside `divK_loopBody`.
    Entry PC of the `divK_addback_step` snippet for `q[j] · b[0]` (the first
    per-limb addback fixup, run only when the trial quotient overshoots).
    Sub-offset relative to the loopBody block
    (= addbackInitOff + 4 = loopBodyOff + 288). -/
abbrev addbackLimb0Off : Word :=  736
/-- Offset of the limb-1 addback step inside `divK_loopBody`.
    Sub-offset relative to the loopBody block
    (= addbackLimb0Off + 32 = loopBodyOff + 320). -/
abbrev addbackLimb1Off : Word :=  768
/-- Offset of the limb-2 addback step inside `divK_loopBody`.
    Sub-offset relative to the loopBody block
    (= addbackLimb1Off + 32 = loopBodyOff + 352). -/
abbrev addbackLimb2Off : Word :=  800
/-- Offset of the limb-3 addback step inside `divK_loopBody`.
    Sub-offset relative to the loopBody block
    (= addbackLimb2Off + 32 = loopBodyOff + 384). -/
abbrev addbackLimb3Off : Word :=  832
/-- Offset of the final addback fixup (`divK_addback_final`) inside
    `divK_loopBody`. The 4-instruction snippet that propagates the final
    addback carry into the high limb, immediately before the addback-skip
    BEQ. Sub-offset relative to the loopBody block
    (= addbackLimb3Off + 32 = addbackBeqOff - 16 = loopBodyOff + 416). -/
abbrev addbackFinalOff : Word :=  864
/-- Offset of the addback-skip BEQ sub-block inside `divK_loopBody`.
    Entry PC of the `BEQ x7, x0, +4` instruction that branches over the
    addback fixup (executed when the trial-quotient `q̂` did NOT overshoot,
    so no addback is needed). Sub-offset relative to the loopBody block
    (= storeLoopOff - 4 = loopBodyOff + 432). -/
abbrev addbackBeqOff : Word :=  880
/-- Offset of the store-quotient sub-block inside `divK_loopBody`.
    Entry PC of the `divK_store_qj` snippet that writes the trial-quotient
    digit `q[j]` to the output buffer (followed by the loop-back / loop-exit
    branch into the next iteration or `divK_denorm`). Sub-offset relative
    to the loopBody block (= loopBodyOff + 436). -/
abbrev storeLoopOff : Word :=  884
/-- Offset of the `divK_loop_control` sub-block inside `divK_loopBody`.
    Entry PC of the 2-instruction snippet (`ADDI x1, ., 4095` + back-jump BGE)
    sandwiched between `divK_store_qj` and `divK_denorm`. Sub-offset relative
    to the loopBody block
    (= storeLoopOff + 16 = denormOff - 8 = loopBackBgeOff - 4 = loopBodyOff + 452). -/
abbrev loopControlOff : Word :=  900
/-- Offset of the loop-back BGE sub-block inside `divK_loopBody`.
    Entry PC of the `BGE x1, x0, -...` instruction at the end of the loop
    body that branches back to `loopBodyOff` for the next iteration when
    `j ≥ 0`, falling through to `denormOff` otherwise. Sub-offset relative
    to the loopBody block (= loopBodyOff + 456 = denormOff - 4). -/
abbrev loopBackBgeOff : Word :=  904
/-- Offset of `divK_denorm` (denormalize result back to original shift). -/
abbrev denormOff    : Word :=  908
/-- Offset of the epilogue (`divK_div_epilogue` for DIV, `divK_mod_epilogue`
    for MOD; both are 40 bytes). -/
abbrev epilogueOff  : Word := 1008
/-- Offset of `divK_zeroPath` (b=0 quick return with result 0). -/
abbrev zeroPathOff  : Word := 1048
/-- Offset of the NOP separator between `divK_zeroPath` and `divK_div128`.
    Ensures the subroutine entry differs from any block exit PC. -/
abbrev nopOff       : Word := 1068
/-- Offset of `divK_div128` (the 128÷64 long-division subroutine). -/
abbrev div128Off    : Word := 1072

/-- Return-site PC of the `divK_div128` call from inside `divK_loopBody`.
    The call sits 68 bytes (17 instructions) into `divK_loopBody`, so the
    JALR-saved return address is `base + loopBodyOff + 68 = base + div128CallRetOff`.
    Used pervasively across `LoopBody*`, `LoopIter*`, `LoopCompose*`,
    `LoopUnified*`, `Compose/FullPath*`, and `Spec/Call*` files. -/
abbrev div128CallRetOff : Word := 516

-- ============================================================================
-- Consistency / drift checks
--
-- Each `drift_check_*` below ties an offset to the sum of the previous offset
-- plus the previous block's length × 4 (bytes per RV64 instruction). If a
-- block grows or shrinks without the corresponding offset being updated, the
-- affected check fails at compile time with a clear error pointing at the
-- stale constant. This localizes address maintenance to this one file.
--
-- These are `example` declarations so they participate in the kernel check
-- without polluting the name space. They resolve by `decide` (all inputs
-- reduce to concrete numerals).
-- ============================================================================

/-- phaseABeqOff = phaseAOff + 28 (sub-block offset within `divK_phaseA`).
    The phaseA-end BEQ to `divK_zeroPath` sits 7 instructions into phaseA. -/
example : phaseABeqOff = phaseAOff + 28 := by decide
example : phaseABeqOff + 4 = phaseBOff := by decide
/-- phaseBOff = phaseAOff + 4 · |divK_phaseA 1020|. -/
example : phaseBOff = phaseAOff + 4 * (divK_phaseA 1020).length := by decide
/-- clzOff = phaseBOff + 4 · |divK_phaseB|. -/
example : clzOff = phaseBOff + 4 * divK_phaseB.length := by decide
/-- phaseC2Off = clzOff + 4 · |divK_clz|. -/
example : phaseC2Off = clzOff + 4 * divK_clz.length := by decide
/-- normBOff = phaseC2Off + 4 · |divK_phaseC2 172|. -/
example : normBOff = phaseC2Off + 4 * (divK_phaseC2 172).length := by decide
/-- normAOff = normBOff + 4 · |divK_normB|. -/
example : normAOff = normBOff + 4 * divK_normB.length := by decide
/-- copyAUOff = normAOff + 4 · |divK_normA 40|. -/
example : copyAUOff = normAOff + 4 * (divK_normA 40).length := by decide
/-- loopSetupOff = copyAUOff + 4 · |divK_copyAU|. -/
example : loopSetupOff = copyAUOff + 4 * divK_copyAU.length := by decide
/-- loopBodyOff = loopSetupOff + 4 · |divK_loopSetup 464|. -/
example : loopBodyOff = loopSetupOff + 4 * (divK_loopSetup 464).length := by decide
/-- denormOff = loopBodyOff + 4 · |divK_loopBody 560 7736|. -/
example : denormOff = loopBodyOff + 4 * (divK_loopBody 560 7736).length := by decide
/-- addbackBeqOff = storeLoopOff - 4 (= loopBodyOff + 432, sub-block offset
    within `divK_loopBody`). The addback-skip BEQ sits one instruction before
    the `divK_store_qj` entry. -/
example : addbackBeqOff = storeLoopOff - 4 := by decide
example : addbackBeqOff = loopBodyOff + 432 := by decide
/-- storeLoopOff = loopBodyOff + 436 (sub-block offset within `divK_loopBody`).
    The `divK_store_qj` snippet starts 109 instructions into the loop body. -/
example : storeLoopOff = loopBodyOff + 436 := by decide
/-- loopControlOff = storeLoopOff + 16 (= loopBodyOff + 452, sub-block offset
    within `divK_loopBody`). The `divK_loop_control` snippet sits 4 instructions
    after the `divK_store_qj` entry. -/
example : loopControlOff = storeLoopOff + 16 := by decide
example : loopControlOff = loopBodyOff + 452 := by decide
example : loopControlOff = loopBackBgeOff - 4 := by decide
/-- loopBackBgeOff = denormOff - 4 (= loopBodyOff + 456, sub-block offset
    within `divK_loopBody`). The loop-back BGE sits one instruction before
    the `divK_denorm` block. -/
example : loopBackBgeOff = denormOff - 4 := by decide
example : loopBackBgeOff = loopBodyOff + 456 := by decide
/-- loopControlOff = storeLoopOff + 16 (= loopBodyOff + 452 = denormOff - 8,
    sub-block offset within `divK_loopBody`). The 2-instruction loop-control
    snippet sits between `divK_store_qj` and `divK_denorm`. -/
example : loopControlOff = storeLoopOff + 16 := by decide
example : loopControlOff = denormOff - 8 := by decide
example : loopControlOff = loopBodyOff + 452 := by decide
/-- correctionSkipBeqOff = loopBodyOff + 280 (sub-block offset within
    `divK_loopBody`). The mulsub correction-skip BEQ sits 70 instructions
    into the loop body. -/
example : correctionSkipBeqOff = loopBodyOff + 280 := by decide
/-- addbackInitOff = correctionSkipBeqOff + 4 (= loopBodyOff + 284, sub-block
    offset within `divK_loopBody`). The add-back carry-init ADDI sits one
    instruction past the correction-skip BEQ (the BEQ's not-taken / fall-through
    target, 71 instructions into the loop body). -/
example : addbackInitOff = correctionSkipBeqOff + 4 := by decide
example : addbackInitOff = loopBodyOff + 284 := by decide
/-- correctionAddbackOff = loopBodyOff + 264 (sub-block offset within
    `divK_loopBody`). The correction-addback path (sub-carry snippet entry)
    sits 66 instructions into the loop body. -/
example : correctionAddbackOff = loopBodyOff + 264 := by decide
/-- addbackLimb{0..3}Off and addbackFinalOff are evenly spaced 32 bytes (8
    instructions) apart starting at `addbackInitOff + 4`, ending at
    `addbackBeqOff - 16` (the 4-instruction `divK_addback_final` fixup before
    the addback-skip BEQ). -/
example : addbackLimb0Off = addbackInitOff + 4 := by decide
example : addbackLimb1Off = addbackLimb0Off + 32 := by decide
example : addbackLimb2Off = addbackLimb1Off + 32 := by decide
example : addbackLimb3Off = addbackLimb2Off + 32 := by decide
example : addbackFinalOff = addbackLimb3Off + 32 := by decide
example : addbackFinalOff + 16 = addbackBeqOff := by decide
example : addbackLimb0Off = loopBodyOff + 288 := by decide
example : addbackFinalOff = loopBodyOff + 416 := by decide
/-- trialCallOff = loopBodyOff + 52 (sub-block offset within `divK_loopBody`).
    The trial-divide call-site sits 13 instructions into the loop body. -/
example : trialCallOff = loopBodyOff + 52 := by decide
/-- trialMaxOff = trialCallOff + 4 (= loopBodyOff + 56, sub-block offset within
    `divK_loopBody`). The `divK_trial_max` snippet is the BLT fall-through one
    instruction past `trialCallOff`. -/
example : trialMaxOff = trialCallOff + 4 := by decide
example : trialMaxOff = loopBodyOff + 56 := by decide
/-- trialJalOff = trialCallOff + 12 (= loopBodyOff + 64, sub-block offset within
    `divK_loopBody`). The JAL-to-`divK_div128` call site sits 16 instructions
    into the loop body, immediately before the div128 call-return PC
    `divCallRetOff = loopBodyOff + 68`. -/
example : trialJalOff = trialCallOff + 12 := by decide
example : trialJalOff = loopBodyOff + 64 := by decide
example : trialJalOff + 4 = div128CallRetOff := by decide
/-- mulsubOff = loopBodyOff + 88 (sub-block offset within `divK_loopBody`).
    The `divK_mulsub_correction` snippet starts 22 instructions into the loop
    body, after the trial-divide entry (~13 instructions) and the div128 call
    site (~9 instructions including the JAL+JALR ABI dance). -/
example : mulsubOff = loopBodyOff + 88 := by decide
/-- correctionSkipOff = loopBodyOff + 176 (sub-block offset within
    `divK_loopBody`). The divK_sub_carry chain on the skip-correction path
    sits 44 instructions into the loop body. -/
example : correctionSkipOff = loopBodyOff + 176 := by decide
/-- epilogueOff = denormOff + 4 · |divK_denorm|. -/
example : epilogueOff = denormOff + 4 * divK_denorm.length := by decide
/-- zeroPathOff = epilogueOff + 4 · |divK_div_epilogue 24|
    (DIV and MOD epilogues share the same length). -/
example : zeroPathOff = epilogueOff + 4 * (divK_div_epilogue 24).length := by decide
example : zeroPathOff = epilogueOff + 4 * (divK_mod_epilogue 24).length := by decide
/-- nopOff = zeroPathOff + 4 · |divK_zeroPath|. -/
example : nopOff = zeroPathOff + 4 * divK_zeroPath.length := by decide
/-- div128Off = nopOff + 4 (single NOP instruction). -/
example : div128Off = nopOff + 4 := by decide
/-- div128CallRetOff = loopBodyOff + 68 (17 instructions into `divK_loopBody`).
    If the prelude of `divK_loopBody` before the JAL to `divK_div128` ever
    changes length, this check fails and points at the constant to update. -/
example : div128CallRetOff = loopBodyOff + 68 := by decide

end EvmAsm.Evm64
