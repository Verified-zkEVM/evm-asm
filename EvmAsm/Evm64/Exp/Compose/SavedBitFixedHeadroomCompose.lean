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

/-- The `ADDI x12 -64` advance-into-headroom block (instruction index 26, byte
    +104) lifted onto the full headroom program.  This is `exp_loop_pointer_restore`
    used as the advance (x12 : evmSp -> evmSp-64). -/
theorem exp_headroom_advance_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 104) (base + 108)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := exp_loop_pointer_restore_spec_within vOld (base + 104)
  simp only [exp_loop_pointer_restore_code] at h
  rw [show (base + 104 + 4 : Word) = base + 108 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 104)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_restore 26
    (by bv_omega)
    (by rfl)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]
      decide)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]
      decide)
    a i ha

/-- The `ADDI x12 +64` pointer-restore block (instruction index 90, byte +360)
    lifted onto the full headroom program.  This is `exp_loop_pointer_advance`
    used as the post-loop restore (x12 : evmSp-64 -> evmSp). -/
theorem exp_headroom_ptr_restore_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 360) (base + 364)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := exp_loop_pointer_advance_spec_within vOld (base + 360)
  simp only [exp_loop_pointer_advance_code] at h
  rw [show (base + 360 + 4 : Word) = base + 364 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 360)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_advance 90
    (by bv_omega)
    (by rfl)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]
      decide)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]
      decide)
    a i ha

end EvmAsm.Evm64.Exp.Compose
