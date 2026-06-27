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

-- ----------------------------------------------------------------------------
-- Full-program lifts of the stack save/restore block specs.  These lift the
-- block specs (over their own `ofProg` code) onto the full save/restore program
-- code requirement, ready to be sequenced with the prologue/loop/epilogue.
-- ----------------------------------------------------------------------------

/-- The stack-save block (idx 10, byte +40) lifted onto the full save/restore
    program: copies the caller words at `evmSp+64..120` into the headroom slack
    at `evmSp-64..-8`. -/
theorem exp_saverestore_save_lifted
    (evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7 h0 h1 h2 h3 h4 h5 h6 h7 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 16 (base + 40) (base + 104)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_loop_stack_save_spec_within evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7
    h0 h1 h2 h3 h4 h5 h6 h7 (base + 40)
  rw [exp_loop_stack_save_code_eq_ofProg] at h
  rw [show (base + 40 + 64 : Word) = base + 104 from by bv_addr] at h
  exact cpsTripleWithin_extend_code
    (exp_saverestore_mono_save base squaringMulOff condMulOff skipOff backOff) h

/-- The stack-restore block (idx 91, byte +364) lifted onto the full save/restore
    program: copies the saved caller words back from the headroom slack at
    `evmSp-64..-8` into `evmSp+64..120`, overwriting the loop's transient
    workspace there (its pre takes arbitrary `g0..g7` at those cells). -/
theorem exp_saverestore_restore_lifted
    (evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7 g0 g1 g2 g3 g4 g5 g6 g7 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 16 (base + 364) (base + 428)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_loop_stack_restore_spec_within evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7
    g0 g1 g2 g3 g4 g5 g6 g7 (base + 364)
  rw [exp_loop_stack_restore_code_eq_ofProg] at h
  rw [show (base + 364 + 64 : Word) = base + 428 from by bv_addr] at h
  exact cpsTripleWithin_extend_code
    (exp_saverestore_mono_restore base squaringMulOff condMulOff skipOff backOff) h

/-- The prologue block (idx 0, byte +0) lifted onto the full save/restore
    program: initializes the accumulator (x5=1, scratch=1,0,0,0), counter
    (x9=256, x20=64), and the exponent cursor/pointer (x19=expLimb3, x16). -/
theorem exp_saverestore_prologue_lifted
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 10 base (base + 40)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
       (.x19 ↦ᵣ expLimb3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) := by
  exact cpsTripleWithin_extend_code
    (exp_saverestore_mono_prologue base squaringMulOff condMulOff skipOff backOff)
    (exp_prologue_fixed_spec_within sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 expLimb3 base)

/-- The epilogue block (idx 107, byte +428) lifted onto the full save/restore
    program: writes the accumulator `r0..r3` (RISC-V scratch `sp+0..24`) to the
    result slot `evmSp+32..56` and advances `x12` by +32 (one EVM-word pop). -/
theorem exp_saverestore_epilogue_lifted
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 9 (base + 428) (base + 464)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_epilogue_spec_within sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 428)
  rw [exp_epilogue_code_eq_ofProg] at h
  rw [show (base + 428 + 36 : Word) = base + 464 from by bv_addr] at h
  exact cpsTripleWithin_extend_code
    (exp_saverestore_mono_epilogue base squaringMulOff condMulOff skipOff backOff) h

-- ----------------------------------------------------------------------------
-- Entry prefix: prologue ;; save ;; advance  (base+0 → base+108).
-- ----------------------------------------------------------------------------

/-- `prologue ;; stack_save` (base+0 → base+104): after initializing the
    accumulator/counter/cursor, back up the caller words at `evmSp+64..120`
    into the headroom slack `evmSp-64..-8`.  `x12` stays at `evmSp`. -/
theorem exp_saverestore_prologue_then_save_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 v6 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 h0 h1 h2 h3 h4 h5 h6 h7 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 26 base (base + 104)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
        (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
        (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) **
       ((.x6 ↦ᵣ v6) **
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
        ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ h7)))
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
        (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
        (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
        (.x19 ↦ᵣ expLimb3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
         ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) **
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
        ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ s7))) := by
  have hp := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) **
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
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (exp_saverestore_prologue_lifted sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 expLimb3 base squaringMulOff condMulOff skipOff backOff)
  have hs := cpsTripleWithin_frameL
    ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
      (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
      (.x19 ↦ᵣ expLimb3) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
       ((0 : Word) + signExtend12 (1 : BitVec 12))) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (exp_saverestore_save_lifted evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7
      h0 h1 h2 h3 h4 h5 h6 h7 base squaringMulOff condMulOff skipOff backOff)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) hp hs

/-- Entry prefix `prologue ;; save ;; advance` (base+0 → base+108): the full
    loop-entry setup with the caller words safely backed up to headroom and the
    EVM stack pointer advanced to the loop's working position `evmSp+64`. -/
theorem exp_saverestore_entry_prefix_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 v6 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 h0 h1 h2 h3 h4 h5 h6 h7 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 27 base (base + 108)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
        (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
        (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) **
       ((.x6 ↦ᵣ v6) **
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
        ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ h7)))
      ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
         (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
         (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
         (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
         (.x19 ↦ᵣ expLimb3) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
          ((0 : Word) + signExtend12 (1 : BitVec 12))) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
         ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) **
        ((.x6 ↦ᵣ s7) **
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
         ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ s7)))) := by
  have h1 := exp_saverestore_prologue_then_save_spec_within sp evmSp cOld tOld
    c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 v6 s0 s1 s2 s3 s4 s5 s6 s7
    h0 h1 h2 h3 h4 h5 h6 h7 base squaringMulOff condMulOff skipOff backOff
  have h2 := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
      (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x16 ↦ᵣ evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12)) **
      (.x19 ↦ᵣ expLimb3) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
       ((0 : Word) + signExtend12 (1 : BitVec 12))) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ expLimb3)) **
     ((.x6 ↦ᵣ s7) **
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
      ((evmSp + signExtend12 ((-8) : BitVec 12)) ↦ₘ s7)))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (exp_saverestore_advance_lifted evmSp base squaringMulOff condMulOff skipOff backOff)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) h1 h2

-- ----------------------------------------------------------------------------
-- Suffix: ptr_restore ;; restore  (base+360 → base+428).
-- ----------------------------------------------------------------------------

/-- `ptr_restore ;; stack_restore` (base+360 → base+428): bring `x12` back from
    the loop's working position `evmSp+64` to `evmSp`, then copy the saved caller
    words from headroom `evmSp-64..-8` back into `evmSp+64..120` (overwriting the
    loop's transient workspace `g0..g7` there). -/
theorem exp_saverestore_ptr_restore_then_restore_spec_within
    (evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7 g0 g1 g2 g3 g4 g5 g6 g7 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 17 (base + 360) (base + 428)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       ((.x6 ↦ᵣ v6) **
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
        ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ g7)))
      ((.x12 ↦ᵣ evmSp) **
       ((.x6 ↦ᵣ s7) **
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
        ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ s7))) := by
  have h1 := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) **
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
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (exp_saverestore_ptr_restore_lifted (evmSp + signExtend12 (64 : BitVec 12)) base
      squaringMulOff condMulOff skipOff backOff)
  rw [show (evmSp + signExtend12 (64 : BitVec 12)) + signExtend12 ((-64) : BitVec 12)
      = evmSp from by
        rw [signExtend12_64, EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64]; bv_omega] at h1
  have h2 := exp_saverestore_restore_lifted evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7
    g0 g1 g2 g3 g4 g5 g6 g7 base squaringMulOff condMulOff skipOff backOff
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) h1 h2

/-- Suffix `ptr_restore ;; restore ;; epilogue` (base+360 → base+464): restore
    the EVM stack pointer and the saved caller words, then write the accumulator
    result `r0..r3` (RISC-V scratch `sp+0..24`) to the result slot `evmSp+32..56`
    and advance `x12` to `evmSp+32` (one EVM-word pop). -/
theorem exp_saverestore_suffix_spec_within
    (sp evmSp v6 tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 g0 g1 g2 g3 g4 g5 g6 g7 : Word)
    (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 26 (base + 360) (base + 464)
      (evm_exp_saverestore_code squaringMulOff condMulOff skipOff backOff base)
      (((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x6 ↦ᵣ v6) **
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
         ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ g7))) **
       ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))
      (((.x6 ↦ᵣ s7) **
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
        ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ s7)) **
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
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3))) := by
  have h1 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (exp_saverestore_ptr_restore_then_restore_spec_within evmSp v6 s0 s1 s2 s3 s4 s5 s6 s7
      g0 g1 g2 g3 g4 g5 g6 g7 base squaringMulOff condMulOff skipOff backOff)
  have h2 := cpsTripleWithin_frameL
    ((.x6 ↦ᵣ s7) **
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
      ((evmSp + signExtend12 (120 : BitVec 12)) ↦ₘ s7))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (exp_saverestore_epilogue_lifted sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base
      squaringMulOff condMulOff skipOff backOff)
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) h1 h2

end EvmAsm.Evm64.Exp.Compose
