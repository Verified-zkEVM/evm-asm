/-
  EvmAsm.Evm64.Exp.LimbSpec

  Per-block / per-limb cpsTriple specs for EXP sub-blocks (square block,
  conditional-multiply block, iter body, loop, prologue, epilogue).

  Slice 4a (beads evm-asm-w5of) lands `exp_bit_test_block_spec_within`.
  Subsequent slices (evm-asm-mtj3 family) will add `exp_square_block_spec`
  and `exp_cond_mul_block_spec`. Per `OPCODE_TEMPLATE.md`, each sub-block
  gets exactly one cpsTriple lemma.
-/

import EvmAsm.Evm64.Exp.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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
  have hb4 : (base + 4 : Word) + 4 = base + 8 := by bv_omega
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
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x9 .x9 (-1)))
      (CodeReq.singleton (base + 4) (.BNE .x9 .x0 backOff)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
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

end EvmAsm.Evm64
