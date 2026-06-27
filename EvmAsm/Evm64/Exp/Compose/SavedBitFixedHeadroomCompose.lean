/-
  Composition scaffolding for the HEADROOM (architecture B) EXP program
  (`evm_exp_msb_saved_bit_two_mul_fixed_headroom`, bug `evm-asm-fjivz`).

  Architecture B runs the squaring loop entirely in the headroom slack: the
  prologue COPIES the operands down into the headroom frame, the loop squares
  there (its MUL workspace lands in the slack, never touching the live stack),
  and the epilogue writes the result back to the standard live slot.  No
  save/restore block is needed (the live stack is framed through untouched), so
  `mul_callable` stays appended after the epilogue with no collision.

  Block layout (byte offsets from `base`):
    prologue        @ +0   (idx 0,  10 instr)
    operand_copy    @ +40  (idx 10, 16 instr)
    advance (-64)   @ +104 (idx 26,  1 instr  = exp_loop_pointer_restore)
    iter_body       @ +108 (idx 27, 63 instr)
    ptr_restore(+64)@ +360 (idx 90,  1 instr  = exp_loop_pointer_advance)
    epilogue        @ +364 (idx 91,  9 instr)
    (exit / mul_callable @ +400)

  This file lifts the individual block specs onto the full headroom program's
  code requirement, mirroring `SavedBitFixedSaveRestoreCompose.lean`.
-/
import EvmAsm.Evm64.Exp.LimbSpec

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The headroom program's code requirement. -/
abbrev evm_exp_headroom_code
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)

/- Corrected headroom layout (bug `evm-asm-fjivz`): the prologue must run at the
   HEADROOM coordinate so its `x16 = evmSp_iter + 48` matches the loop and it
   reads the COPIED exponent.  Order:
     operand_copy @0 (16) ;; pointer_restore @16 (-64) ;; pointer_restore @17 (-64)
     ;; prologue @18 (10) ;; pointer_advance @28 (+64) ;; iter_body @29 (63)
     ;; pointer_advance @92 (+64) ;; epilogue @93 (9)
   102 instr / 408 bytes; loop body @ byte +116, exit (= mul) @ +408. -/

/-- First `ADDI x12 -64` (instr idx 16, byte +64): x12 evmSp -> evmSp-64. -/
theorem exp_headroom_advance1_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 64) (base + 68)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := exp_loop_pointer_restore_spec_within vOld (base + 64)
  simp only [exp_loop_pointer_restore_code] at h
  rw [show (base + 64 + 4 : Word) = base + 68 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 64)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_restore 16
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- Second `ADDI x12 -64` (instr idx 17, byte +68): x12 evmSp-64 -> evmSp-128. -/
theorem exp_headroom_advance2_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 68) (base + 72)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := exp_loop_pointer_restore_spec_within vOld (base + 68)
  simp only [exp_loop_pointer_restore_code] at h
  rw [show (base + 68 + 4 : Word) = base + 72 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 68)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_restore 17
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- `ADDI x12 +64` into the loop (instr idx 28, byte +112): x12 evmSp-128 -> evmSp-64. -/
theorem exp_headroom_loop_advance_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 112) (base + 116)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := exp_loop_pointer_advance_spec_within vOld (base + 112)
  simp only [exp_loop_pointer_advance_code] at h
  rw [show (base + 112 + 4 : Word) = base + 116 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 112)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_advance 28
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- `ADDI x12 +64` out of the loop (instr idx 92, byte +368): x12 evmSp-64 -> evmSp. -/
theorem exp_headroom_ptr_restore_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 368) (base + 372)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := exp_loop_pointer_advance_spec_within vOld (base + 368)
  simp only [exp_loop_pointer_advance_code] at h
  rw [show (base + 368 + 4 : Word) = base + 372 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 368)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_advance 92
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

end EvmAsm.Evm64.Exp.Compose
