/-
  Composition scaffolding for the SAVE/RESTORE EXP program
  (`evm_exp_msb_saved_bit_two_mul_fixed_saverestore`, bug `evm-asm-fjivz`).

  The save/restore fix wraps the proven loop with two stack blocks that back up
  and restore the caller stack words at `evmSp+64..120` (which the loop transiently
  uses as MUL workspace) into the headroom slack `evmSp-64..-8`, so the caller's
  `rest` is preserved — making EXP a correct standard opcode.

  This file lifts the individual block specs (`LimbSpec.lean`) onto the full
  save/restore program's code requirement, so they can be sequenced into the
  boundary-level spec.  Each lift is `cpsTripleWithin_extend_code` over
  `CodeReq.ofProg_mono_sub` with the block's contiguous slice of the program.
-/
import EvmAsm.Evm64.Exp.LimbSpec

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The save/restore program's code requirement. -/
abbrev evm_exp_saverestore_code
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)

/-- The `ADDI x12 +64` pointer-advance block (instruction index 26, byte +104)
    lifted onto the full save/restore program. -/
theorem exp_saverestore_advance_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 104) (base + 108)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := exp_loop_pointer_advance_spec_within vOld (base + 104)
  simp only [exp_loop_pointer_advance_code] at h
  rw [show (base + 104 + 4 : Word) = base + 108 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 104)
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_advance 26
    (by bv_omega)
    (by rfl)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]
      decide)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]
      decide)
    a i ha

/-- The `ADDI x12 -64` pointer-restore block (instruction index 90, byte +360)
    lifted onto the full save/restore program. -/
theorem exp_saverestore_ptr_restore_lifted
    (vOld base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 1 (base + 360) (base + 364)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := exp_loop_pointer_restore_spec_within vOld (base + 360)
  simp only [exp_loop_pointer_restore_code] at h
  rw [show (base + 360 + 4 : Word) = base + 364 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 360)
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_pointer_restore 90
    (by bv_omega)
    (by rfl)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]
      decide)
    (by
      rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]
      decide)
    a i ha

-- ----------------------------------------------------------------------------
-- Reusable code-req subsumption facts: each `ofProg`-based block of the
-- save/restore program is a sub-requirement of the full program code.  These
-- feed `cpsTripleWithin_extend_code` to lift any block spec onto the full
-- program during sequencing (the loop body is excluded — its code req is the
-- separate `…CanonicalAppendedMulCode`, bridged elsewhere).
-- ----------------------------------------------------------------------------

/-- prologue block (idx 0, byte +0) ⊆ full save/restore program. -/
theorem exp_saverestore_mono_prologue
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    ∀ a i, (CodeReq.ofProg base exp_prologue_fixed) a = some i →
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base) a = some i :=
  CodeReq.ofProg_mono_sub base base
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)
    exp_prologue_fixed 0
    (by bv_omega) (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)

/-- stack-save block (idx 10, byte +40) ⊆ full save/restore program. -/
theorem exp_saverestore_mono_save
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    ∀ a i, (CodeReq.ofProg (base + 40) exp_loop_stack_save) a = some i →
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base) a = some i :=
  CodeReq.ofProg_mono_sub base (base + 40)
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_stack_save 10
    (by bv_omega) (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)

/-- stack-restore block (idx 91, byte +364) ⊆ full save/restore program. -/
theorem exp_saverestore_mono_restore
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    ∀ a i, (CodeReq.ofProg (base + 364) exp_loop_stack_restore) a = some i →
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base) a = some i :=
  CodeReq.ofProg_mono_sub base (base + 364)
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_stack_restore 91
    (by bv_omega) (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)

/-- epilogue block (idx 107, byte +428) ⊆ full save/restore program. -/
theorem exp_saverestore_mono_epilogue
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    ∀ a i, (CodeReq.ofProg (base + 428) exp_epilogue) a = some i →
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base) a = some i :=
  CodeReq.ofProg_mono_sub base (base + 428)
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff)
    exp_epilogue 107
    (by bv_omega) (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]; decide)

end EvmAsm.Evm64.Exp.Compose
