/-
  EvmAsm.Evm64.DivMod.Callable

  LP64-callable shims around `evm_div` / `evm_mod`.

  Per the corrected layout (PR #2376), the
  shim is **not** `evm_div ;; cc_ret`: appending `cc_ret` to the program
  text would place it at byte 1268, unreachable from `evm_div`'s exit
  PC. Instead we **replace the NOP** at the existing exit slot with
  `cc_ret`, keeping every other instruction at exactly the same offset
  (so internal branch targets — including `divK_loopBody`'s
  `subr_off = 556` into `divK_div128_v4` — remain valid).

      evm_div  := … ;; ADDI .x0 .x0 0       ;; divK_div128_v4
      evm_div_callable
              := … ;; cc_ret                 ;; divK_div128_v4

  Same total instruction count (1:1 NOP↔cc_ret swap), same byte length
  (1372 bytes = 343 instructions), same exit PC (the slot that holds
  the swapped instruction sits at the same byte offset as the original
  NOP).

  This file is **prep slice A** for evm-asm-8pfe / GH #90: it
  introduces only the Program definitions and length lemmas.
  Code-region helpers, sub-code lemmas and the
  `_function_spec` round-trip will land in follow-up slices.

  Reference: GH #90 (parent evm-asm-34sg), beads slice evm-asm-0tnux.
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.Compose.Base
import EvmAsm.Evm64.DivMod.Compose.V4NoNop
import EvmAsm.Evm64.DivMod.Spec.Unified
import EvmAsm.Evm64.DivMod.Spec.ModBzeroNoNop
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Program definitions
-- ============================================================================

/-- LP64-callable wrapper for `evm_div`: swap the NOP at the exit slot
    with `cc_ret`. Every other phase / sub-block, including the
    appended `divK_div128_v4` subroutine and all internal branch offsets,
    is kept at exactly the same instruction index as in `evm_div`. -/
def evm_div_callable : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;            -- replaces the NOP at the exit slot
  divK_div128_v4

/-- LP64-callable wrapper for `evm_mod`: same shape as
    `evm_div_callable`, with `divK_mod_epilogue` for the remainder
    output. -/
def evm_mod_callable : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;            -- replaces the NOP at the exit slot
  divK_div128_v4

/-- v4 LP64-callable wrapper for `evm_div`, using the corrected
    `divK_div128_v4` subroutine. This is a code-surface helper for the v4
    migration; existing callable specs remain on `evm_div_callable` until the
    dispatcher proofs are lifted to v4. -/
def evm_div_callable_v4 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128_v4

/-- v4 LP64-callable wrapper for `evm_mod`, using the corrected
    `divK_div128_v4` subroutine. -/
def evm_mod_callable_v4 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128_v4

/-- `cc_ret = JALR x0 x1 0` is exactly one instruction. -/
theorem cc_ret_len : cc_ret.length = 1 := by decide

theorem evm_div_callable_length : evm_div_callable.length = 343 := by
  unfold evm_div_callable
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_v4_len]

theorem evm_mod_callable_length : evm_mod_callable.length = 343 := by
  unfold evm_mod_callable
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_modEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_v4_len]

theorem evm_div_callable_byte_length : 4 * evm_div_callable.length = 1372 := by
  rw [evm_div_callable_length]

theorem evm_mod_callable_byte_length : 4 * evm_mod_callable.length = 1372 := by
  rw [evm_mod_callable_length]

theorem evm_div_callable_v4_length : evm_div_callable_v4.length = 343 := by
  unfold evm_div_callable_v4
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_v4_len]

theorem evm_mod_callable_v4_length : evm_mod_callable_v4.length = 343 := by
  unfold evm_mod_callable_v4
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_modEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_v4_len]

theorem evm_div_callable_v4_byte_length :
    4 * evm_div_callable_v4.length = 1372 := by
  rw [evm_div_callable_v4_length]

theorem evm_mod_callable_v4_byte_length :
    4 * evm_mod_callable_v4.length = 1372 := by
  rw [evm_mod_callable_v4_length]

-- ============================================================================
-- CodeReq abbreviations
-- ============================================================================

/-- 14-block CodeReq layout for `evm_div_callable`. Identical to `divCode`
    (see `Evm64/DivMod/Compose/Base.lean`) except block 12 — the NOP at
    `nopOff = 1068` — is replaced with `cc_ret_code (base + nopOff)` to
    match the NOP↔`cc_ret` swap performed in `evm_div_callable`'s Program
    definition. All other blocks (including the appended `divK_div128_v4`
    subroutine at `div128Off = 1072`) keep the same offset, so internal
    branch targets remain valid.

    No equality bridge with `CodeReq.ofProg base evm_div_callable` is
    proved here; that is a follow-up slice. -/
abbrev evm_div_callable_code (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),                          -- block 12: NOP ↔ cc_ret swap
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- 14-block CodeReq layout for `evm_mod_callable`. Identical to
    `evm_div_callable_code` except block 10 uses `divK_mod_epilogue`
    (mirrors `modCode` vs `divCode` in `Compose/Base.lean`). -/
abbrev evm_mod_callable_code (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),                          -- block 12: NOP ↔ cc_ret swap
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- 14-block CodeReq layout for `evm_div_callable_v4`. -/
abbrev evm_div_callable_code_v4 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- 14-block CodeReq layout for `evm_mod_callable_v4`. -/
abbrev evm_mod_callable_code_v4 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

-- ============================================================================
-- Equality bridges with CodeReq.ofProg
--
-- These connect the 14-block `unionAll` abbreviations with the canonical
-- `CodeReq.ofProg base ·` form produced by `evm_div_callable` /
-- `evm_mod_callable`'s 13-`;;` sequence. The proof iterates
-- `CodeReq.ofProg_append` 13 times, normalizing the running base offset to
-- the named constant from `Compose/Offsets.lean` after each step. Mirrors
-- `evm_mul_code_eq_ofProg` (Multiply/LimbSpec.lean) and `expLoopCode_eq_*`
-- (Exp/Compose/Base.lean) — same pattern, longer chain.
-- ============================================================================

open EvmAsm.Rv64.CodeReq in
theorem evm_div_callable_code_eq_ofProg (base : Word) :
    evm_div_callable_code base = CodeReq.ofProg base evm_div_callable := by
  unfold evm_div_callable_code evm_div_callable cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  -- Block 0 → 1: phaseA ;; rest, advance offset to phaseBOff = 32.
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  -- Block 1 → 2: phaseB, advance to clzOff = 116.
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  -- Block 2 → 3: clz, advance to phaseC2Off = 212.
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  -- Block 3 → 4: phaseC2, advance to normBOff = 228.
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  -- Block 4 → 5: normB, advance to normAOff = 312.
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  -- Block 5 → 6: normA, advance to copyAUOff = 396.
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  -- Block 6 → 7: copyAU, advance to loopSetupOff = 432.
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  -- Block 7 → 8: loopSetup, advance to loopBodyOff = 448.
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  -- Block 8 → 9: loopBody, advance to denormOff = 908.
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  -- Block 9 → 10: denorm, advance to epilogueOff = 1008.
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  -- Block 10 → 11: div_epilogue, advance to zeroPathOff = 1048.
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_div_epilogue 24).length) =
        base + zeroPathOff by rw [divK_divEpilogue_len]; bv_omega]
  -- Block 11 → 12: zeroPath, advance to nopOff = 1068 (the cc_ret slot).
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  -- Block 12 → 13: cc_ret (single instruction), advance to div128Off = 1072.
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

-- Per-block subsumption lemmas for evm_div_callable_code / evm_mod_callable_code
--
-- Mirror the `shared_b*_div` / `shared_b*_mod` pattern from
-- `EvmAsm.Evm64.DivMod.Compose.Base`. Index `N` uses the divCode/modCode
-- block numbering (0..13). Block 12 is `cc_ret_code (base + nopOff)`
-- instead of the NOP — the offset is identical (both length 1), so the
-- disjointness side conditions match modulo a `cc_ret.length = 1` fact.
-- ============================================================================

/-- Variant of `skipBlock` (from `Compose.Base`) that also knows
    `cc_ret.length = 1`. Needed when the block-being-skipped is
    `cc_ret_code` rather than an `ofProg`-of-named-program, since the
    disjointness `bv_omega` asks for the program length. -/
macro "skipBlockCC" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len, divK_div128_v2_len,
          divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- v5 callable program variants (over `divK_div128_v5`)
--
-- Mirror of the v4 callable surfaces, swapping the appended div128 subroutine
-- to `divK_div128_v5` (the capped Knuth-D variant). `divK_div128_v5` is 85
-- instructions (vs v4's 75), so the callable length grows 343 → 353 and the
-- byte length 1372 → 1412. Every other block / branch offset is unchanged
-- (div128 sits last, after `cc_ret`). Bead evm-asm-wbc4i.7.3 (V5.7c).
-- ============================================================================

/-- v5 LP64-callable wrapper for `evm_div`, using the capped `divK_div128_v5`
    subroutine. -/
def evm_div_callable_v5 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128_v5

/-- v5 LP64-callable wrapper for `evm_mod`, using the capped `divK_div128_v5`
    subroutine. -/
def evm_mod_callable_v5 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128_v5

theorem evm_div_callable_v5_length : evm_div_callable_v5.length = 353 := by
  unfold evm_div_callable_v5
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_v5_len]

theorem evm_mod_callable_v5_length : evm_mod_callable_v5.length = 353 := by
  unfold evm_mod_callable_v5
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_modEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_v5_len]

theorem evm_div_callable_v5_byte_length :
    4 * evm_div_callable_v5.length = 1412 := by
  rw [evm_div_callable_v5_length]

theorem evm_mod_callable_v5_byte_length :
    4 * evm_mod_callable_v5.length = 1412 := by
  rw [evm_mod_callable_v5_length]

/-- 14-block CodeReq layout for `evm_div_callable_v5`. -/
abbrev evm_div_callable_code_v5 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128_v5
  ]

/-- 14-block CodeReq layout for `evm_mod_callable_v5`. -/
abbrev evm_mod_callable_code_v5 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128_v5
  ]

open EvmAsm.Rv64.CodeReq in
theorem evm_div_callable_code_v5_eq_ofProg (base : Word) :
    evm_div_callable_code_v5 base = CodeReq.ofProg base evm_div_callable_v5 := by
  unfold evm_div_callable_code_v5 evm_div_callable_v5 cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_div_epilogue 24).length) =
        base + zeroPathOff by rw [divK_divEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

open EvmAsm.Rv64.CodeReq in
theorem evm_mod_callable_code_v5_eq_ofProg (base : Word) :
    evm_mod_callable_code_v5 base = CodeReq.ofProg base evm_mod_callable_v5 := by
  unfold evm_mod_callable_code_v5 evm_mod_callable_v5 cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_mod_epilogue 24).length) =
        base + zeroPathOff by rw [divK_modEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

-- Canonical callable specs live in the split files:
-- * CallableV1Legacy.lean keeps the legacy v1 surfaces for existing callers.
-- * CallableV4Div.lean and CallableV4Mod.lean carry the v4 proof surfaces.

end EvmAsm.Evm64
