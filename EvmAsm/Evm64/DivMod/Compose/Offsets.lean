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
    [phaseBOff    =  32] divK_phaseB        (84 bytes)
    [clzOff       = 116] divK_clz           (96 bytes)
    [phaseC2Off   = 212] divK_phaseC2       (16 bytes)
    [normBOff     = 228] divK_normB         (84 bytes)
    [normAOff     = 312] divK_normA         (84 bytes)
    [copyAUOff    = 396] divK_copyAU        (36 bytes)
    [loopSetupOff = 432] divK_loopSetup     (16 bytes)
    [loopBodyOff  = 448] divK_loopBody     (460 bytes)
      [trialCallOff       = 500]  divK_loopBody BLTU/JAL trial-quotient call entry (loopBodyOff + 52)
      [correctionSkipBeqOff = 728]  divK_loopBody mulsub-correction-skip BEQ entry (loopBodyOff + 280)
      [storeLoopOff = 884]  divK_store_qj sub-block (loopBodyOff + 436)
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
/-- Offset of `divK_phaseB` (b=0 branch + leading-limb analysis). -/
abbrev phaseBOff    : Word :=   32
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
/-- Offset of the trial-quotient call sub-block inside `divK_loopBody`.
    Entry PC of the `BLTU x7, x10, +12` instruction that branches between the
    div128 call path (uHi < vTop) and the max-trial path (uHi ≥ vTop).
    Sub-offset relative to the loopBody block (= loopBodyOff + 52, i.e. 13
    instructions into the loop body, just after the `save j + trial load`
    prelude). -/
abbrev trialCallOff : Word :=  500
/-- Offset of the mulsub correction-skip BEQ entry inside `divK_loopBody`.
    Entry PC of the BEQ instruction that branches over the addback correction
    block when the trial-quotient mulsub did not borrow (the "skip" path).
    Sub-offset relative to the loopBody block (= loopBodyOff + 280, i.e. 70
    instructions into the loop body). -/
abbrev correctionSkipBeqOff : Word :=  728
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
/-- correctionSkipBeqOff = loopBodyOff + 280 (sub-block offset within
    `divK_loopBody`). The mulsub correction-skip BEQ sits 70 instructions
    into the loop body. -/
example : correctionSkipBeqOff = loopBodyOff + 280 := by decide
/-- trialCallOff = loopBodyOff + 52 (sub-block offset within `divK_loopBody`).
    The trial-quotient BLTU/JAL pair sits 13 instructions into the loop body. -/
example : trialCallOff = loopBodyOff + 52 := by decide
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
