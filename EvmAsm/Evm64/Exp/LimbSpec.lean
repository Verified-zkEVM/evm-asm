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

end EvmAsm.Evm64
