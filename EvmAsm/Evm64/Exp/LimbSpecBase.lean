/-
  EvmAsm.Evm64.Exp.LimbSpecBase

  First half of `EvmAsm.Evm64.Exp.LimbSpec`, split out to keep each file under
  the file-size guardrail (`scripts/check-file-size.sh`). `LimbSpec` imports
  this module and re-exports it transitively, so importers are unaffected.

  Per-block / per-limb cpsTriple specs for EXP sub-blocks (square block,
  conditional-multiply block, iter body, loop, prologue, epilogue).

  Slice 4a (beads evm-asm-w5of) lands `exp_bit_test_block_spec_within`.
  Subsequent slices (evm-asm-mtj3 family) will add `exp_square_block_spec`
  and `exp_cond_mul_block_spec`. Per `OPCODE_TEMPLATE.md`, each sub-block
  gets exactly one cpsTriple lemma.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (ADDI Assertion CodeReq LD SD addi_spec_gen_same_within
  addi_spec_gen_within andi_spec_gen_within beq_spec_within bne_spec_gen_within
  cpsBranchWithin cpsBranchWithin_extend_code cpsBranchWithin_frameR
  cpsBranchWithin_ntakenPath cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
  cpsBranchWithin_takenPath cpsBranchWithin_takenStripPure2 cpsBranchWithin_weaken
  cpsTripleWithin cpsTripleWithin_extend_code cpsTripleWithin_frameR
  cpsTripleWithin_mono_nSteps cpsTripleWithin_seq_perm_same_cr cpsTripleWithin_seq_same_cr
  cpsTripleWithin_seq_cpsBranchWithin_with_perm cpsTripleWithin_weaken
  generic_sd_spec_within jal_spec_within ld_spec_gen_within seq sepConj_pure_right
  signExtend12 signExtend13 signExtend21 single slli_spec_gen_same_within
  srli_spec_gen_same_within srli_spec_gen_within)

-- ============================================================================
-- Section 1: exp_bit_test_block (3 instructions, slice 4a / evm-asm-w5of)
-- ============================================================================
--
-- `exp_bit_test_block` (defined in `Exp/Program.lean`):
--
--     ANDI .x10 .x5 1 ;;       -- x10 := x5 &&& 1 (current low bit)
--     SRLI .x5  .x5 1 ;;       -- x5  := x5 >>> 1 (advance bit cursor)
--     ADDI .x6  .x6 (-1)       -- x6  := x6 - 1   (decrement remaining bits)
--
-- This is the leaf bit-test atom of the square-and-multiply per-iteration
-- body. The ANDI/SRLI/ADDI triple does NOT touch memory and only depends
-- on the values currently in x5, x6, x10 (with x0 frame-preserved).
-- Mirrors the leading triple of `shr_phase_b_spec_within` in
-- `Evm64/Shift/LimbSpec.lean`.

abbrev exp_bit_test_block_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_bit_test_block

theorem exp_bit_test_block_spec_within
    (e c v10 : Word) (base : Word) :
    let code := exp_bit_test_block_code base
    cpsTripleWithin 3 base (base + 12) code
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) := by
  have AN := andi_spec_gen_within .x10 .x5 v10 e 1 base (by nofun)
  have SR := srli_spec_gen_same_within .x5 e 1 (base + 4) (by nofun)
  have AD := addi_spec_gen_same_within .x6 c (-1) (base + 8) (by nofun)
  runBlock AN SR AD

/-- Corrected MSB-first bit-test atom for the square-result EXP algorithm. -/
abbrev exp_msb_bit_test_block_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_msb_bit_test_block

theorem exp_msb_bit_test_block_spec_within
    (e c v10 : Word) (base : Word) :
    let code := exp_msb_bit_test_block_code base
    cpsTripleWithin 3 base (base + 12) code
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat))) := by
  have SR := srli_spec_gen_within .x10 .x5 v10 e 63 base (by nofun)
  have SL := slli_spec_gen_same_within .x5 e 1 (base + 4) (by nofun)
  have AD := addi_spec_gen_same_within .x6 c (-1) (base + 8) (by nofun)
  runBlock SR SL AD

/-- Save the tested EXP bit before the following `mul_callable` clobbers
    caller-saved argument/result registers. -/
abbrev exp_save_bit_block_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_save_bit_block

theorem exp_save_bit_block_spec_within
    (bit v18 : Word) (base : Word) :
    let code := exp_save_bit_block_code base
    cpsTripleWithin 1 base (base + 4) code
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base exp_save_bit_block) _ _
  rw [show CodeReq.ofProg base exp_save_bit_block =
      CodeReq.singleton base (.ADDI .x18 .x10 0) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_within .x18 .x10 v18 bit 0 base (by nofun)

-- ============================================================================
-- Section 2: exp_square_block (1 instruction, slice 4b / evm-asm-4219)
-- ============================================================================
--
-- `exp_square_block mulOff` (defined in `Exp/Program.lean`):
--
--     JAL .x1 mulOff
--
-- Single near-`JAL` invoking `mul_callable`. This is the unconditional
-- squaring step of the per-iteration body: control transfers to
-- `base + signExtend21 mulOff` and `.x1` is updated with the return
-- address `base + 4`. Argument-marshalling (placing both factors in the
-- LP64 a-slots) is handled by the surrounding scaffold and is not part of
-- this leaf cpsTriple. Mirrors `rlp_phase3_single_byte_spec_within`'s
-- single-instruction `ofProg → singleton` shape.

abbrev exp_square_block_code (base : Word) (mulOff : BitVec 21) : CodeReq :=
  CodeReq.ofProg base (exp_square_block mulOff)

theorem exp_square_block_spec_within
    (mulOff : BitVec 21) (vOld : Word) (base : Word) :
    let code := exp_square_block_code base mulOff
    cpsTripleWithin 1 base (base + signExtend21 mulOff) code
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 4)) := by
  show cpsTripleWithin 1 base (base + signExtend21 mulOff)
    (CodeReq.ofProg base (exp_square_block mulOff)) _ _
  rw [show CodeReq.ofProg base (exp_square_block mulOff) =
      CodeReq.singleton base (.JAL .x1 mulOff) from CodeReq.ofProg_singleton]
  exact jal_spec_within .x1 vOld mulOff base (by nofun)

-- ============================================================================
-- Section 3: exp_cond_mul_block (2 instructions, slice 4c / evm-asm-a0vp)
-- ============================================================================
--
-- `exp_cond_mul_block mulOff skipOff` (defined in `Exp/Program.lean`):
--
--     BEQ .x10 .x0 skipOff ;;     -- if x10 == 0 (current bit is zero), skip
--     JAL .x1 mulOff              -- otherwise call mul_callable
--
-- Two-instruction conditional-multiply branch: the BEQ skips past the JAL
-- when the current exponent bit (`x10`) is zero, otherwise the JAL invokes
-- `mul_callable` and updates `.x1` with the return address `(base + 4) + 4
-- = base + 8`. As with `exp_square_block`, argument-marshalling is handled
-- by the surrounding scaffold and is not part of this leaf cpsBranch.
--
-- Mirrors the BEQ-into-instruction shape from `divK_div128_clamp_q*`
-- (`DivMod/LimbSpec/Div128Clamp.lean`), but emits a `cpsBranchWithin` (two
-- exits) rather than a merged `cpsTripleWithin`, because the surrounding
-- `exp_iter_body` composition cares about which path the iteration took.

abbrev exp_cond_mul_block_code (base : Word)
    (mulOff : BitVec 21) (skipOff : BitVec 13) : CodeReq :=
  CodeReq.ofProg base (exp_cond_mul_block mulOff skipOff)

theorem exp_cond_mul_block_spec_within
    (mulOff : BitVec 21) (skipOff : BitVec 13) (v10 vOld : Word) (base : Word) :
    cpsBranchWithin 2 base (exp_cond_mul_block_code base mulOff skipOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ vOld))
      (base + signExtend13 skipOff)
        ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ vOld) ** ⌜v10 = 0⌝)
      ((base + 4) + signExtend21 mulOff)
        ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ (base + 8)) ** ⌜v10 ≠ 0⌝) := by
  -- Reshape the 2-instruction `ofProg` CodeReq into a union of singletons.
  have hcr_eq : exp_cond_mul_block_code base mulOff skipOff =
      (CodeReq.singleton base (.BEQ .x10 .x0 skipOff)).union
        (CodeReq.singleton (base + 4) (.JAL .x1 mulOff)) := by
    show CodeReq.ofProg base [.BEQ .x10 .x0 skipOff, .JAL .x1 mulOff] = _
    exact CodeReq.ofProg_pair
  -- Step 1: BEQ at base, framed with (.x1 ↦ᵣ vOld), extended to the full cr.
  have hbeq := beq_spec_within .x10 .x0 skipOff v10 (0 : Word) base
  have hbeq_framed := cpsBranchWithin_frameR (.x1 ↦ᵣ vOld) (by pcFree) hbeq
  have hbeq_ext : cpsBranchWithin 1 base
      (exp_cond_mul_block_code base mulOff skipOff)
      (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word))) ** (.x1 ↦ᵣ vOld))
      (base + signExtend13 skipOff)
        (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = (0 : Word)⌝) **
         (.x1 ↦ᵣ vOld))
      (base + 4)
        (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ (0 : Word)⌝) **
         (.x1 ↦ᵣ vOld)) :=
    cpsBranchWithin_extend_code (h := hbeq_framed) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]
      intro h
      split at h <;> simp_all)
  -- Step 2: JAL at base + 4, framed with x10/x0/⌜v10 ≠ 0⌝, extended to cr.
  have hjal_raw := jal_spec_within .x1 vOld mulOff (base + 4) (by nofun)
  have hjal_framed := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ (0 : Word)⌝)
    (by pcFree) hjal_raw
  have hb4 : (base + 4 : Word) + 4 = base + 8 :=
    EvmAsm.Evm64.Exp.AddrNorm.expSingleInstrNextPc base
  rw [hb4] at hjal_framed
  have hjal_ext : cpsTripleWithin 1 (base + 4)
      ((base + 4) + signExtend21 mulOff)
      (exp_cond_mul_block_code base mulOff skipOff)
      ((.x1 ↦ᵣ vOld) **
       ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ (0 : Word)⌝))
      ((.x1 ↦ᵣ (base + 8)) **
       ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ (0 : Word)⌝)) :=
    cpsTripleWithin_extend_code (h := hjal_framed) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]
      intro h
      split at h <;> simp_all)
  -- Compose: BEQ ntaken path (v10 ≠ 0) flows into JAL; taken path exits.
  have composed := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    (h1 := hbeq_ext)
    (hperm := fun h hp => by xperm_hyp hp)
    (h2 := hjal_ext)
    (ht1 := fun h hp => hp)
  -- Permute pre and posts into the natural right-associated shape.
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

-- ============================================================================
-- Section 4: exp_loop_back (2 instructions, slice 4d / evm-asm-smfg)
-- ============================================================================
--
-- `exp_loop_back backOff` (defined in `Exp/Program.lean`):
--
--     ADDI .x9 .x9 (-1) ;;          -- decrement master iteration counter
--     single (.BNE .x9 .x0 backOff) -- branch back to loop top while x9 ≠ 0
--
-- Tail of the EXP square-and-multiply loop. After the ADDI, the master
-- counter `x9` is decremented by one. If the post-decrement value is
-- nonzero, the BNE is taken (PC := (base+4) + signExtend13 backOff,
-- i.e. branch back to the iteration head); otherwise control falls
-- through to `base + 8` (loop exit).
--
-- Mirrors `signext_cascade_step_spec_within`'s shape (single-register
-- ADDI feeding into a BNE/BEQ pair). Argument-marshalling and the
-- surrounding 256-iteration scaffold land in evm-asm-w5mk.

abbrev exp_loop_back_code (backOff : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (exp_loop_back backOff)

theorem exp_loop_back_spec_within (c : Word) (backOff : BitVec 13)
    (base target : Word) (htarget : (base + 4) + signExtend13 backOff = target) :
    let cNew := c + signExtend12 ((-1 : BitVec 12))
    let code := exp_loop_back_code backOff base
    cpsBranchWithin 2 base code
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew ≠ 0⌝)
      (base + 8) ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew = 0⌝) := by
  -- Reshape the two-instruction CodeReq.
  show cpsBranchWithin 2 base
    (CodeReq.ofProg base (exp_loop_back backOff)) _ _ _ _ _
  rw [show CodeReq.ofProg base (exp_loop_back backOff) =
      (CodeReq.singleton base (.ADDI .x9 .x9 (-1))).union
        (CodeReq.singleton (base + 4) (.BNE .x9 .x0 backOff)) by
    show CodeReq.ofProg base
        (ADDI .x9 .x9 (-1) ;; single (.BNE .x9 .x0 backOff)) = _
    show CodeReq.ofProg base [.ADDI .x9 .x9 (-1), .BNE .x9 .x0 backOff] = _
    exact CodeReq.ofProg_pair]
  have ha1 : (base + 4 : Word) + 4 = base + 8 :=
    EvmAsm.Evm64.Exp.AddrNorm.expSingleInstrNextPc base
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x9 .x9 (-1)))
      (CodeReq.singleton (base + 4) (.BNE .x9 .x0 backOff)) :=
    CodeReq.Disjoint.singleton (EvmAsm.Evm64.Exp.AddrNorm.expBase_ne_add4 base)
  -- Step 1: ADDI x9 x9 -1 — frame x0 across.
  have s1_raw := addi_spec_gen_same_within .x9 c (-1) base (by nofun)
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x9 .x9 (-1)))
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) s1_raw
  -- Step 2: BNE x9 x0 backOff — taken when x9' ≠ 0.
  have s2_raw := bne_spec_gen_within .x9 .x0 backOff
    (c + signExtend12 ((-1) : BitVec 12)) (0 : Word) (base + 4)
  rw [htarget, ha1] at s2_raw
  -- Compose ADDI ;; BNE; clean perms.
  exact cpsTripleWithin_seq_cpsBranchWithin_with_perm hd
    (fun _ hp => hp) s1 s2_raw

-- ============================================================================
-- Section 4.5: exp_loop_pointer_advance / exp_loop_pointer_restore
-- (each 1 instruction, slice evm-asm-133cl)
-- ============================================================================
--
-- `exp_loop_pointer_advance` and `exp_loop_pointer_restore` (defined in
-- `Exp/Program.lean`) are single-instruction ADDI blocks that adjust the EVM
-- stack pointer `x12` by ±64 bytes between the EXP prologue and the
-- 256-iteration square-and-multiply loop body. The full-loop composition
-- (slice evm-asm-w5mk) wires them around the loop with `cpsTriple_seq`.
-- Mirrors the single-instruction `ofProg → singleton` shape of
-- `exp_square_block_spec_within`.

abbrev exp_loop_pointer_advance_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_loop_pointer_advance

theorem exp_loop_pointer_advance_spec_within
    (vOld : Word) (base : Word) :
    let code := exp_loop_pointer_advance_code base
    cpsTripleWithin 1 base (base + 4) code
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base exp_loop_pointer_advance) _ _
  rw [show CodeReq.ofProg base exp_loop_pointer_advance =
      CodeReq.singleton base (.ADDI .x12 .x12 64) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_same_within .x12 vOld 64 base (by nofun)

abbrev exp_loop_pointer_restore_code (base : Word) : CodeReq :=
  CodeReq.ofProg base exp_loop_pointer_restore

theorem exp_loop_pointer_restore_spec_within
    (vOld : Word) (base : Word) :
    let code := exp_loop_pointer_restore_code base
    cpsTripleWithin 1 base (base + 4) code
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base exp_loop_pointer_restore) _ _
  rw [show CodeReq.ofProg base exp_loop_pointer_restore =
      CodeReq.singleton base (.ADDI .x12 .x12 (-64)) from CodeReq.ofProg_singleton]
  exact addi_spec_gen_same_within .x12 vOld (-64) base (by nofun)

-- ============================================================================
-- Section 5: exp_prologue (6 instructions, slice 4e / evm-asm-20z6.1)
-- ============================================================================

def exp_prologue_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.ADDI .x9 .x0 256)).union
    ((CodeReq.singleton (base + 4) (.ADDI .x5 .x0 1)).union
      ((CodeReq.singleton (base + 8) (.SD .x2 .x5 0)).union
        ((CodeReq.singleton (base + 12) (.SD .x2 .x0 8)).union
          ((CodeReq.singleton (base + 16) (.SD .x2 .x0 16)).union
            (CodeReq.singleton (base + 20) (.SD .x2 .x0 24))))))

theorem exp_prologue_code_eq_ofProg (base : Word) :
    exp_prologue_code base = CodeReq.ofProg base exp_prologue := by
  unfold exp_prologue_code exp_prologue ADDI SD single seq
  change _ = CodeReq.ofProg base
    [.ADDI .x9 .x0 256, .ADDI .x5 .x0 1, .SD .x2 .x5 0,
     .SD .x2 .x0 8, .SD .x2 .x0 16, .SD .x2 .x0 24]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem exp_prologue_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 6 base (base + 24) (exp_prologue_code base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  unfold exp_prologue_code
  have hCounter := addi_spec_gen_within .x9 .x0 cOld (0 : Word)
    (256 : BitVec 12) base (by decide)
  have hOne := addi_spec_gen_within .x5 .x0 tOld (0 : Word)
    (1 : BitVec 12) (base + 4) (by decide)
  have hSd0 := generic_sd_spec_within .x2 .x5 sp
    ((0 : Word) + signExtend12 (1 : BitVec 12)) m0
    (0 : BitVec 12) (base + 8)
  have hSd1 := generic_sd_spec_within .x2 .x0 sp (0 : Word) m1
    (8 : BitVec 12) (base + 12)
  have hSd2 := generic_sd_spec_within .x2 .x0 sp (0 : Word) m2
    (16 : BitVec 12) (base + 16)
  have hSd3 := generic_sd_spec_within .x2 .x0 sp (0 : Word) m3
    (24 : BitVec 12) (base + 20)
  runBlock hCounter hOne hSd0 hSd1 hSd2 hSd3

theorem exp_prologue_ofProg_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base exp_prologue)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) := by
  rw [← exp_prologue_code_eq_ofProg]
  exact exp_prologue_spec_within sp cOld tOld m0 m1 m2 m3 base

/-- The four result limbs initialized by `exp_prologue` fold to the EVM word
    value `1`, which is the accumulator seed for square-and-multiply. -/
theorem exp_prologue_result_word_one (sp : Word) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word))) =
    evmWordIs sp (1 : EvmWord) := by
  have h0 : (sp + signExtend12 (0 : BitVec 12) : Word) = sp := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h1 : ((0 : Word) + signExtend12 (1 : BitVec 12)) = (1 : Word) := by decide
  have h8 : (sp + signExtend12 (8 : BitVec 12) : Word) = sp + 8 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h16 : (sp + signExtend12 (16 : BitVec 12) : Word) = sp + 16 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h24 : (sp + signExtend12 (24 : BitVec 12) : Word) = sp + 24 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  rw [h0, h1, h8, h16, h24, evmWordIs_one]

/-- Right-associated variant of `exp_prologue_result_word_one` for composition
    postconditions with a framed remainder. -/
theorem exp_prologue_result_word_one_right (sp : Word) (Q : Assertion) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) ** Q) =
    (evmWordIs sp (1 : EvmWord) ** Q) := by
  have h0 : (sp + signExtend12 (0 : BitVec 12) : Word) = sp := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h1 : ((0 : Word) + signExtend12 (1 : BitVec 12)) = (1 : Word) := by
    decide
  have h8 : (sp + signExtend12 (8 : BitVec 12) : Word) = sp + 8 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h16 : (sp + signExtend12 (16 : BitVec 12) : Word) = sp + 16 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  have h24 : (sp + signExtend12 (24 : BitVec 12) : Word) = sp + 24 := by
    simp only [EvmAsm.Rv64.signExtend12, BitVec.reduceSignExtend]; bv_omega
  rw [h0, h1, h8, h16, h24]
  rw [evmWordIs_one_right]

/-- Consumer-facing prologue spec with the initialized accumulator folded into
    the stack-word assertion used by later EXP composition proofs. -/
theorem exp_prologue_word_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base exp_prologue)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord)) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => by
      rw [← exp_prologue_result_word_one sp]
      xperm_hyp hq)
    (exp_prologue_ofProg_spec_within sp cOld tOld m0 m1 m2 m3 base)

-- ============================================================================
-- Section 6: exp_epilogue (9 instructions, slice 4f / evm-asm-20z6.2)
-- ============================================================================

def exp_epilogue_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x5 .x2 0)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x5 32)).union
      ((CodeReq.singleton (base + 8) (.LD .x5 .x2 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x5 40)).union
          ((CodeReq.singleton (base + 16) (.LD .x5 .x2 16)).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x5 48)).union
              ((CodeReq.singleton (base + 24) (.LD .x5 .x2 24)).union
                ((CodeReq.singleton (base + 28) (.SD .x12 .x5 56)).union
                  (CodeReq.singleton (base + 32) (.ADDI .x12 .x12 32)))))))))

theorem exp_epilogue_code_eq_ofProg (base : Word) :
    exp_epilogue_code base = CodeReq.ofProg base exp_epilogue := by
  unfold exp_epilogue_code exp_epilogue LD SD ADDI single seq
  change _ = CodeReq.ofProg base
    [.LD .x5 .x2 0, .SD .x12 .x5 32, .LD .x5 .x2 8,
     .SD .x12 .x5 40, .LD .x5 .x2 16, .SD .x12 .x5 48,
     .LD .x5 .x2 24, .SD .x12 .x5 56, .ADDI .x12 .x12 32]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_singleton]
  bv_addr

theorem exp_epilogue_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 base (base + 36) (exp_epilogue_code base)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) := by
  unfold exp_epilogue_code
  have hLd0 := ld_spec_gen_within .x5 .x2 sp tOld r0
    (0 : BitVec 12) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x5 evmSp r0 d0
    (32 : BitVec 12) (base + 4)
  have hLd1 := ld_spec_gen_within .x5 .x2 sp r0 r1
    (8 : BitVec 12) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x5 evmSp r1 d1
    (40 : BitVec 12) (base + 12)
  have hLd2 := ld_spec_gen_within .x5 .x2 sp r1 r2
    (16 : BitVec 12) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x5 evmSp r2 d2
    (48 : BitVec 12) (base + 20)
  have hLd3 := ld_spec_gen_within .x5 .x2 sp r2 r3
    (24 : BitVec 12) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x5 evmSp r3 d3
    (56 : BitVec 12) (base + 28)
  have hAddSp := addi_spec_gen_same_within .x12 evmSp
    (32 : BitVec 12) (base + 32) (by decide)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3 hAddSp

theorem exp_epilogue_ofProg_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 base (base + 36) (CodeReq.ofProg base exp_epilogue)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) := by
  rw [← exp_epilogue_code_eq_ofProg]
  exact exp_epilogue_spec_within sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base

-- ============================================================================
-- Section 5.6: exp_loop_stack_save / exp_loop_stack_restore (bug evm-asm-fjivz)
-- ============================================================================
--
-- Straight-line specs for the two blocks that preserve the caller EVM-stack
-- words at `evmSp + 64 .. + 120` across the loop, by copying them to/from the
-- free headroom at `evmSp - 64 .. - 8`. Both run with `x12 = evmSp` and use
-- `x6` as the copy temporary. Source cells are at small positive offsets;
-- headroom cells are at `signExtend12`-negative offsets.

def exp_loop_stack_save_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x6 .x12 64)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x6 (-64))).union
      ((CodeReq.singleton (base + 8) (.LD .x6 .x12 72)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x6 (-56))).union
          ((CodeReq.singleton (base + 16) (.LD .x6 .x12 80)).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x6 (-48))).union
              ((CodeReq.singleton (base + 24) (.LD .x6 .x12 88)).union
                ((CodeReq.singleton (base + 28) (.SD .x12 .x6 (-40))).union
                  ((CodeReq.singleton (base + 32) (.LD .x6 .x12 96)).union
                    ((CodeReq.singleton (base + 36) (.SD .x12 .x6 (-32))).union
                      ((CodeReq.singleton (base + 40) (.LD .x6 .x12 104)).union
                        ((CodeReq.singleton (base + 44) (.SD .x12 .x6 (-24))).union
                          ((CodeReq.singleton (base + 48) (.LD .x6 .x12 112)).union
                            ((CodeReq.singleton (base + 52) (.SD .x12 .x6 (-16))).union
                              ((CodeReq.singleton (base + 56) (.LD .x6 .x12 120)).union
                                (CodeReq.singleton (base + 60)
                                  (.SD .x12 .x6 (-8)))))))))))))))))

theorem exp_loop_stack_save_code_eq_ofProg (base : Word) :
    exp_loop_stack_save_code base = CodeReq.ofProg base exp_loop_stack_save := by
  unfold exp_loop_stack_save_code exp_loop_stack_save LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x6 .x12 64, .SD .x12 .x6 (-64), .LD .x6 .x12 72, .SD .x12 .x6 (-56),
     .LD .x6 .x12 80, .SD .x12 .x6 (-48), .LD .x6 .x12 88, .SD .x12 .x6 (-40),
     .LD .x6 .x12 96, .SD .x12 .x6 (-32), .LD .x6 .x12 104, .SD .x12 .x6 (-24),
     .LD .x6 .x12 112, .SD .x12 .x6 (-16), .LD .x6 .x12 120, .SD .x12 .x6 (-8)]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  bv_addr

def exp_loop_operand_copy_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x6 .x12 0)).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x6 (-128))).union
      ((CodeReq.singleton (base + 8) (.LD .x6 .x12 8)).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x6 (-120))).union
          ((CodeReq.singleton (base + 16) (.LD .x6 .x12 16)).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x6 (-112))).union
              ((CodeReq.singleton (base + 24) (.LD .x6 .x12 24)).union
                ((CodeReq.singleton (base + 28) (.SD .x12 .x6 (-104))).union
                  ((CodeReq.singleton (base + 32) (.LD .x6 .x12 32)).union
                    ((CodeReq.singleton (base + 36) (.SD .x12 .x6 (-96))).union
                      ((CodeReq.singleton (base + 40) (.LD .x6 .x12 40)).union
                        ((CodeReq.singleton (base + 44) (.SD .x12 .x6 (-88))).union
                          ((CodeReq.singleton (base + 48) (.LD .x6 .x12 48)).union
                            ((CodeReq.singleton (base + 52) (.SD .x12 .x6 (-80))).union
                              ((CodeReq.singleton (base + 56) (.LD .x6 .x12 56)).union
                                (CodeReq.singleton (base + 60)
                                  (.SD .x12 .x6 (-72)))))))))))))))))

theorem exp_loop_operand_copy_code_eq_ofProg (base : Word) :
    exp_loop_operand_copy_code base = CodeReq.ofProg base exp_loop_operand_copy := by
  unfold exp_loop_operand_copy_code exp_loop_operand_copy LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x6 .x12 0, .SD .x12 .x6 (-128), .LD .x6 .x12 8, .SD .x12 .x6 (-120),
     .LD .x6 .x12 16, .SD .x12 .x6 (-112), .LD .x6 .x12 24, .SD .x12 .x6 (-104),
     .LD .x6 .x12 32, .SD .x12 .x6 (-96), .LD .x6 .x12 40, .SD .x12 .x6 (-88),
     .LD .x6 .x12 48, .SD .x12 .x6 (-80), .LD .x6 .x12 56, .SD .x12 .x6 (-72)]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  bv_addr

/-- Arch-B operand copy: copies live `base` (`evmSp+0..24`) and `exponent`
    (`evmSp+32..56`) into the headroom loop frame (`base → evmSp-128..-104`,
    `exponent → evmSp-96..-72`). Runs with `x12 = evmSp` (live top); the live
    stack at `evmSp+64..` is untouched. The headroom destination cells start
    arbitrary (`h0..h7`) and end holding the copied operands. -/
theorem exp_loop_operand_copy_spec_within
    (evmSp v6 b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 : Word)
    (base : Word) :
    cpsTripleWithin 16 base (base + 64) (exp_loop_operand_copy_code base)
      ((.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7))
      ((.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ e3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-128) : BitVec 12)) ↦ₘ b0) **
       ((evmSp + signExtend12 ((-120) : BitVec 12)) ↦ₘ b1) **
       ((evmSp + signExtend12 ((-112) : BitVec 12)) ↦ₘ b2) **
       ((evmSp + signExtend12 ((-104) : BitVec 12)) ↦ₘ b3) **
       ((evmSp + signExtend12 ((-96) : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 ((-88) : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3)) := by
  unfold exp_loop_operand_copy_code
  have hLd0 := ld_spec_gen_within .x6 .x12 evmSp v6 b0 (0) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x6 evmSp b0 h0 (-128) (base + 4)
  have hLd1 := ld_spec_gen_within .x6 .x12 evmSp b0 b1 (8) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x6 evmSp b1 h1 (-120) (base + 12)
  have hLd2 := ld_spec_gen_within .x6 .x12 evmSp b1 b2 (16) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x6 evmSp b2 h2 (-112) (base + 20)
  have hLd3 := ld_spec_gen_within .x6 .x12 evmSp b2 b3 (24) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x6 evmSp b3 h3 (-104) (base + 28)
  have hLd4 := ld_spec_gen_within .x6 .x12 evmSp b3 e0 (32) (base + 32) (by decide)
  have hSd4 := generic_sd_spec_within .x12 .x6 evmSp e0 h4 (-96) (base + 36)
  have hLd5 := ld_spec_gen_within .x6 .x12 evmSp e0 e1 (40) (base + 40) (by decide)
  have hSd5 := generic_sd_spec_within .x12 .x6 evmSp e1 h5 (-88) (base + 44)
  have hLd6 := ld_spec_gen_within .x6 .x12 evmSp e1 e2 (48) (base + 48) (by decide)
  have hSd6 := generic_sd_spec_within .x12 .x6 evmSp e2 h6 (-80) (base + 52)
  have hLd7 := ld_spec_gen_within .x6 .x12 evmSp e2 e3 (56) (base + 56) (by decide)
  have hSd7 := generic_sd_spec_within .x12 .x6 evmSp e3 h7 (-72) (base + 60)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3 hLd4 hSd4 hLd5 hSd5 hLd6 hSd6
    hLd7 hSd7

theorem exp_loop_stack_save_spec_within
    (evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7 h0 h1 h2 h3 h4 h5 h6 h7 : Word)
    (base : Word) :
    cpsTripleWithin 16 base (base + 64) (exp_loop_stack_save_code base)
      ((.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 (64 : BitVec 12)) ↦ₘ s0) **
       ((evmSp + signExtend12 (72 : BitVec 12)) ↦ₘ s1) **
       ((evmSp + signExtend12 (80 : BitVec 12)) ↦ₘ s2) **
       ((evmSp + signExtend12 (88 : BitVec 12)) ↦ₘ s3) **
       ((evmSp + signExtend12 (96 : BitVec 12)) ↦ₘ s4) **
       ((evmSp + signExtend12 (104 : BitVec 12)) ↦ₘ s5) **
       ((evmSp + signExtend12 (112 : BitVec 12)) ↦ₘ s6) **
       ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ s7) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ h0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ h1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ h2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ h3) **
       ((evmSp + signExtend12 ((-32) : BitVec 12)) ↦ₘ h4) **
       ((evmSp + signExtend12 ((-24) : BitVec 12)) ↦ₘ h5) **
       ((evmSp + signExtend12 ((-16) : BitVec 12)) ↦ₘ h6) **
       ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ h7))
      ((.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ s7) **
       ((evmSp + signExtend12 (64 : BitVec 12)) ↦ₘ s0) **
       ((evmSp + signExtend12 (72 : BitVec 12)) ↦ₘ s1) **
       ((evmSp + signExtend12 (80 : BitVec 12)) ↦ₘ s2) **
       ((evmSp + signExtend12 (88 : BitVec 12)) ↦ₘ s3) **
       ((evmSp + signExtend12 (96 : BitVec 12)) ↦ₘ s4) **
       ((evmSp + signExtend12 (104 : BitVec 12)) ↦ₘ s5) **
       ((evmSp + signExtend12 (112 : BitVec 12)) ↦ₘ s6) **
       ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ s7) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ s0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ s1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ s2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ s3) **
       ((evmSp + signExtend12 ((-32) : BitVec 12)) ↦ₘ s4) **
       ((evmSp + signExtend12 ((-24) : BitVec 12)) ↦ₘ s5) **
       ((evmSp + signExtend12 ((-16) : BitVec 12)) ↦ₘ s6) **
       ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ s7)) := by
  unfold exp_loop_stack_save_code
  have hLd0 := ld_spec_gen_within .x6 .x12 evmSp v6 s0 (64) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x6 evmSp s0 h0 (-64) (base + 4)
  have hLd1 := ld_spec_gen_within .x6 .x12 evmSp s0 s1 (72) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x6 evmSp s1 h1 (-56) (base + 12)
  have hLd2 := ld_spec_gen_within .x6 .x12 evmSp s1 s2 (80) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x6 evmSp s2 h2 (-48) (base + 20)
  have hLd3 := ld_spec_gen_within .x6 .x12 evmSp s2 s3 (88) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x6 evmSp s3 h3 (-40) (base + 28)
  have hLd4 := ld_spec_gen_within .x6 .x12 evmSp s3 s4 (96) (base + 32) (by decide)
  have hSd4 := generic_sd_spec_within .x12 .x6 evmSp s4 h4 (-32) (base + 36)
  have hLd5 := ld_spec_gen_within .x6 .x12 evmSp s4 s5 (104) (base + 40) (by decide)
  have hSd5 := generic_sd_spec_within .x12 .x6 evmSp s5 h5 (-24) (base + 44)
  have hLd6 := ld_spec_gen_within .x6 .x12 evmSp s5 s6 (112) (base + 48) (by decide)
  have hSd6 := generic_sd_spec_within .x12 .x6 evmSp s6 h6 (-16) (base + 52)
  have hLd7 := ld_spec_gen_within .x6 .x12 evmSp s6 s7 (120) (base + 56) (by decide)
  have hSd7 := generic_sd_spec_within .x12 .x6 evmSp s7 h7 (-8) (base + 60)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3 hLd4 hSd4 hLd5 hSd5 hLd6 hSd6
    hLd7 hSd7

def exp_loop_stack_restore_code (base : Word) : CodeReq :=
  (CodeReq.singleton base (.LD .x6 .x12 (-64))).union
    ((CodeReq.singleton (base + 4) (.SD .x12 .x6 64)).union
      ((CodeReq.singleton (base + 8) (.LD .x6 .x12 (-56))).union
        ((CodeReq.singleton (base + 12) (.SD .x12 .x6 72)).union
          ((CodeReq.singleton (base + 16) (.LD .x6 .x12 (-48))).union
            ((CodeReq.singleton (base + 20) (.SD .x12 .x6 80)).union
              ((CodeReq.singleton (base + 24) (.LD .x6 .x12 (-40))).union
                ((CodeReq.singleton (base + 28) (.SD .x12 .x6 88)).union
                  ((CodeReq.singleton (base + 32) (.LD .x6 .x12 (-32))).union
                    ((CodeReq.singleton (base + 36) (.SD .x12 .x6 96)).union
                      ((CodeReq.singleton (base + 40) (.LD .x6 .x12 (-24))).union
                        ((CodeReq.singleton (base + 44) (.SD .x12 .x6 104)).union
                          ((CodeReq.singleton (base + 48) (.LD .x6 .x12 (-16))).union
                            ((CodeReq.singleton (base + 52) (.SD .x12 .x6 112)).union
                              ((CodeReq.singleton (base + 56) (.LD .x6 .x12 (-8))).union
                                (CodeReq.singleton (base + 60)
                                  (.SD .x12 .x6 120))))))))))))))))

theorem exp_loop_stack_restore_code_eq_ofProg (base : Word) :
    exp_loop_stack_restore_code base = CodeReq.ofProg base exp_loop_stack_restore := by
  unfold exp_loop_stack_restore_code exp_loop_stack_restore LD SD single seq
  change _ = CodeReq.ofProg base
    [.LD .x6 .x12 (-64), .SD .x12 .x6 64, .LD .x6 .x12 (-56), .SD .x12 .x6 72,
     .LD .x6 .x12 (-48), .SD .x12 .x6 80, .LD .x6 .x12 (-40), .SD .x12 .x6 88,
     .LD .x6 .x12 (-32), .SD .x12 .x6 96, .LD .x6 .x12 (-24), .SD .x12 .x6 104,
     .LD .x6 .x12 (-16), .SD .x12 .x6 112, .LD .x6 .x12 (-8), .SD .x12 .x6 120]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_singleton]
  bv_addr

theorem exp_loop_stack_restore_spec_within
    (evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7 g0 g1 g2 g3 g4 g5 g6 g7 : Word)
    (base : Word) :
    cpsTripleWithin 16 base (base + 64) (exp_loop_stack_restore_code base)
      ((.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ s0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ s1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ s2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ s3) **
       ((evmSp + signExtend12 ((-32) : BitVec 12)) ↦ₘ s4) **
       ((evmSp + signExtend12 ((-24) : BitVec 12)) ↦ₘ s5) **
       ((evmSp + signExtend12 ((-16) : BitVec 12)) ↦ₘ s6) **
       ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ s7) **
       ((evmSp + signExtend12 (64 : BitVec 12)) ↦ₘ g0) **
       ((evmSp + signExtend12 (72 : BitVec 12)) ↦ₘ g1) **
       ((evmSp + signExtend12 (80 : BitVec 12)) ↦ₘ g2) **
       ((evmSp + signExtend12 (88 : BitVec 12)) ↦ₘ g3) **
       ((evmSp + signExtend12 (96 : BitVec 12)) ↦ₘ g4) **
       ((evmSp + signExtend12 (104 : BitVec 12)) ↦ₘ g5) **
       ((evmSp + signExtend12 (112 : BitVec 12)) ↦ₘ g6) **
       ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ g7))
      ((.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ s7) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ s0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ s1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ s2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ s3) **
       ((evmSp + signExtend12 ((-32) : BitVec 12)) ↦ₘ s4) **
       ((evmSp + signExtend12 ((-24) : BitVec 12)) ↦ₘ s5) **
       ((evmSp + signExtend12 ((-16) : BitVec 12)) ↦ₘ s6) **
       ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ s7) **
       ((evmSp + signExtend12 (64 : BitVec 12)) ↦ₘ s0) **
       ((evmSp + signExtend12 (72 : BitVec 12)) ↦ₘ s1) **
       ((evmSp + signExtend12 (80 : BitVec 12)) ↦ₘ s2) **
       ((evmSp + signExtend12 (88 : BitVec 12)) ↦ₘ s3) **
       ((evmSp + signExtend12 (96 : BitVec 12)) ↦ₘ s4) **
       ((evmSp + signExtend12 (104 : BitVec 12)) ↦ₘ s5) **
       ((evmSp + signExtend12 (112 : BitVec 12)) ↦ₘ s6) **
       ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ s7)) := by
  unfold exp_loop_stack_restore_code
  have hLd0 := ld_spec_gen_within .x6 .x12 evmSp v6 s0 (-64) base (by decide)
  have hSd0 := generic_sd_spec_within .x12 .x6 evmSp s0 g0 (64) (base + 4)
  have hLd1 := ld_spec_gen_within .x6 .x12 evmSp s0 s1 (-56) (base + 8) (by decide)
  have hSd1 := generic_sd_spec_within .x12 .x6 evmSp s1 g1 (72) (base + 12)
  have hLd2 := ld_spec_gen_within .x6 .x12 evmSp s1 s2 (-48) (base + 16) (by decide)
  have hSd2 := generic_sd_spec_within .x12 .x6 evmSp s2 g2 (80) (base + 20)
  have hLd3 := ld_spec_gen_within .x6 .x12 evmSp s2 s3 (-40) (base + 24) (by decide)
  have hSd3 := generic_sd_spec_within .x12 .x6 evmSp s3 g3 (88) (base + 28)
  have hLd4 := ld_spec_gen_within .x6 .x12 evmSp s3 s4 (-32) (base + 32) (by decide)
  have hSd4 := generic_sd_spec_within .x12 .x6 evmSp s4 g4 (96) (base + 36)
  have hLd5 := ld_spec_gen_within .x6 .x12 evmSp s4 s5 (-24) (base + 40) (by decide)
  have hSd5 := generic_sd_spec_within .x12 .x6 evmSp s5 g5 (104) (base + 44)
  have hLd6 := ld_spec_gen_within .x6 .x12 evmSp s5 s6 (-16) (base + 48) (by decide)
  have hSd6 := generic_sd_spec_within .x12 .x6 evmSp s6 g6 (112) (base + 52)
  have hLd7 := ld_spec_gen_within .x6 .x12 evmSp s6 s7 (-8) (base + 56) (by decide)
  have hSd7 := generic_sd_spec_within .x12 .x6 evmSp s7 g7 (120) (base + 60)
  runBlock hLd0 hSd0 hLd1 hSd1 hLd2 hSd2 hLd3 hSd3 hLd4 hSd4 hLd5 hSd5 hLd6 hSd6
    hLd7 hSd7


end EvmAsm.Evm64
