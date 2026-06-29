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
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedFinalChain

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The headroom program's code requirement. -/
abbrev evm_exp_headroom_code
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)

/-- Canonical headroom EXP code with the callable MUL routine appended at the
    exit address. This is the code surface shared by the entry prefix and the
    lifted 256-iteration loop body. -/
abbrev evm_exp_headroom_canonical_appended_mul_code (base : Word) : CodeReq :=
  (evm_exp_headroom_code
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base).union
    (mul_callable_code (base + 408))

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

/-- Operand-copy block (instr idx 0, byte +0..64) lifted onto the headroom program. -/
theorem exp_headroom_operand_copy_lifted
    (evmSp v6 b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 16 base (base + 64)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_loop_operand_copy_spec_within evmSp v6 b0 b1 b2 b3 e0 e1 e2 e3
    h0 h1 h2 h3 h4 h5 h6 h7 base
  rw [exp_loop_operand_copy_code_eq_ofProg] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base base
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_loop_operand_copy 0
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- Prologue block (instr idx 18, byte +72..112) lifted onto the headroom program.
    Runs at the headroom coordinate `x12 = evmSp` (= `evmSp_live - 128` in use). -/
theorem exp_headroom_prologue_lifted
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 expLimb3 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 10 (base + 72) (base + 112)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_prologue_fixed_spec_within sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 expLimb3 (base + 72)
  simp only [exp_prologue_fixed_code] at h
  rw [show (base + 72 + 40 : Word) = base + 112 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 72)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_prologue_fixed 18
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- Epilogue block (instr idx 93, byte +372..408) lifted onto the headroom program.
    Runs at `x12 = evmSp` (= `evmSp_live` in use); writes result @ `evmSp+32`. -/
theorem exp_headroom_epilogue_lifted
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 9 (base + 372) (base + 408)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
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
  have h := exp_epilogue_spec_within sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 372)
  rw [exp_epilogue_code_eq_ofProg] at h
  rw [show (base + 372 + 36 : Word) = base + 408 from by bv_addr] at h
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.ofProg_mono_sub base (base + 372)
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff)
    exp_epilogue 93
    (by bv_omega)
    (by rfl)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
    a i ha

/-- Union head-monotonicity for the loop lift: the canonical iter-body slice sits
    inside the headroom program (idx 29), and the appended `mul_callable` at
    `base+408` is disjoint from the headroom code (which ends at `base+408`). -/
theorem exp_headroom_loop_code_mono (base : Word) :
    ∀ a i,
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode (base + 72 + 44)
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).union
          (mul_callable_code (base + 72 + 336))) a = some i →
      ((evm_exp_headroom_code
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base).union
          (mul_callable_code (base + 408))) a = some i := by
  intro a i hq
  rw [show (base + 72 + 336 : Word) = base + 408 from by bv_addr] at hq
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg] at hq
  -- iter-body slice ⊆ headroom code at idx 29
  have hsub : ∀ a i, CodeReq.ofProg (base + 72 + 44)
      (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff) a = some i →
      evm_exp_headroom_code
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base a = some i := by
    intro a' i' h'
    refine CodeReq.ofProg_mono_sub base (base + 72 + 44)
      (evm_exp_msb_saved_bit_two_mul_fixed_headroom
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      29 (by bv_addr) (by rfl)
      (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length,
              EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length]; decide)
      (by rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]; decide)
      a' i' h'
  cases hib : CodeReq.ofProg (base + 72 + 44)
      (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff) a with
  | some j =>
    rw [CodeReq.union_mono_left a j hib] at hq
    have hji : j = i := by simpa using hq
    subst hji
    exact CodeReq.union_mono_left a j (hsub a j hib)
  | none =>
    rw [CodeReq.union_none_left hib] at hq
    -- hq : mul_callable_code (base+408) a = some i ; show headroom a = none then union
    have hq' := hq
    rw [mul_callable_code_eq_ofProg] at hq'
    obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hq'
    rw [EvmAsm.Evm64.mul_callable_length] at hk
    have hnone : evm_exp_headroom_code
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base a = none := by
      unfold evm_exp_headroom_code
      apply CodeReq.ofProg_none_range
      intro k' hk'
      rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length] at hk'
      rw [haddr]; bv_omega
    rw [CodeReq.union_none_left hnone]; exact hq

/-- The body-only loop surface (n=255 iterations) lifted onto the headroom program
    at code base `base+72` (iter body @ byte +116, mul @ base+408). -/
theorem exp_headroom_loop_lifted
    (sp evmSp base : Word) (baseWord exponentWord dWord eWord : EvmWord)
    (rest : List EvmWord) (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 72 + 44) (base + 72 + 296)
      ((evm_exp_headroom_code
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base).union
          (mul_callable_code (base + 408)))
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
          baseWord exponentWord
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
        evmStackIs (evmSp + 128) rest) := by
  have h := exp_final_loop_firstIterPreWithResidual_bodyonly (base + 72) sp evmSp
    baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase
  refine cpsTripleWithin_extend_code ?_ h
  intro a i hq
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq] at hq
  exact exp_headroom_loop_code_mono base a i hq


/-- Folded-post wrapper for `exp_headroom_loop_lifted`. -/
theorem exp_headroom_loop_lifted_folded
    (sp evmSp base : Word) (baseWord exponentWord dWord eWord : EvmWord)
    (rest : List EvmWord) (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 72 + 44) (base + 72 + 296)
      ((evm_exp_headroom_code
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base).union
          (mul_callable_code (base + 408)))
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest) := by
  rw [expFinalLoopFirstIterPost_unfold]
  exact exp_headroom_loop_lifted sp evmSp base baseWord exponentWord dWord eWord rest
    lookahead vOld v18 hbase


/-- Framed variant of `exp_headroom_loop_lifted_folded`, for composing the
    headroom loop while carrying the untouched live-stack resources. -/
theorem exp_headroom_loop_lifted_folded_framed
    (sp evmSp base : Word) (baseWord exponentWord dWord eWord : EvmWord)
    (rest : List EvmWord) (lookahead vOld v18 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 72 + 44) (base + 72 + 296)
      ((evm_exp_headroom_code
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff base).union
          (mul_callable_code (base + 408)))
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest ** F)
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest ** F) :=
  cpsTripleWithin_frameR F hF
    (exp_headroom_loop_lifted_folded sp evmSp base baseWord exponentWord dWord eWord rest
      lookahead vOld v18 hbase)


/-- Folded loop theorem stated against the canonical appended-code abbreviation. -/
theorem exp_headroom_loop_lifted_folded_canonical_appended
    (sp evmSp base : Word) (baseWord exponentWord dWord eWord : EvmWord)
    (rest : List EvmWord) (lookahead vOld v18 : Word)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 72 + 44) (base + 72 + 296)
      (evm_exp_headroom_canonical_appended_mul_code base)
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest) :=
  exp_headroom_loop_lifted_folded sp evmSp base baseWord exponentWord dWord eWord rest
    lookahead vOld v18 hbase

/-- Framed canonical-code variant of `exp_headroom_loop_lifted_folded`. -/
theorem exp_headroom_loop_lifted_folded_canonical_appended_framed
    (sp evmSp base : Word) (baseWord exponentWord dWord eWord : EvmWord)
    (rest : List EvmWord) (lookahead vOld v18 : Word)
    (F : Assertion) (hF : F.pcFree)
    (hbase : (base + 72 + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 72 + 44) (base + 72 + 296)
      (evm_exp_headroom_canonical_appended_mul_code base)
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest ** F)
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest ** F) :=
  cpsTripleWithin_frameR F hF
    (exp_headroom_loop_lifted_folded_canonical_appended sp evmSp base
      baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase)

/-- Entry prefix `operand_copy ;; advance1(-64) ;; advance2(-64) ;; prologue`
    (base+0 → base+112): copies the live operands into the headroom frame, walks
    `x12` down to `evmSp-128`, then runs the prologue at that headroom coordinate.
    The shared cell `evmSp-72` carries the copied exponent limb 3 (= prologue's
    `expLimb3`). -/
theorem exp_headroom_entry_prefix_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 28 base (base + 112)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
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
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 ((-64) : BitVec 12))) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
                  + signExtend12 (-8 : BitVec 12))) **
       (.x19 ↦ᵣ e3) ** (.x6 ↦ᵣ e3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
  -- operand_copy (base+0 → base+64)
  have h_oc := exp_headroom_operand_copy_lifted evmSp v6 b0 b1 b2 b3 e0 e1 e2 e3
    h0 h1 h2 h3 h4 h5 h6 h7 base squaringMulOff condMulOff skipOff backOff
  -- advance1 (base+64 → base+68): x12 evmSp → evmSp-64
  have h_a1 := exp_headroom_advance1_lifted evmSp base squaringMulOff condMulOff
    skipOff backOff
  -- advance2 (base+68 → base+72): x12 evmSp-64 → evmSp-128
  have h_a2 := exp_headroom_advance2_lifted (evmSp + signExtend12 ((-64) : BitVec 12))
    base squaringMulOff condMulOff skipOff backOff
  -- prologue (base+72 → base+112) at x12 = evmSp-128.  Normalize the prologue's
  -- exponent-limb cell `(evmSp-128)+56` to the operand_copy headroom cell `evmSp-72`,
  -- and its `x12 = evmSp-128`.
  have hptr72 : (evmSp + signExtend12 ((-64) : BitVec 12)
      + signExtend12 ((-64) : BitVec 12)) + signExtend12 (56 : BitVec 12)
      = evmSp + signExtend12 ((-72) : BitVec 12) := by bv_addr
  have h_pro := exp_headroom_prologue_lifted sp
    (evmSp + signExtend12 ((-64) : BitVec 12) + signExtend12 ((-64) : BitVec 12))
    cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 e3 base
    squaringMulOff condMulOff skipOff backOff
  rw [hptr72] at h_pro
  -- Frame the prologue-ambient state around operand_copy.
  have h_oc' := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) ** (.x5 ↦ᵣ tOld) **
     (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
     ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_oc
  -- Thread x12 down through the two advances (everything else framed).
  have h_a1f := cpsTripleWithin_frameL
    ((.x6 ↦ᵣ e3) **
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
     ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3) **
     (.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) ** (.x5 ↦ᵣ tOld) **
     (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
     ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_a1
  have h_oc_a1 := cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) h_oc' h_a1f
  have h_a2f := cpsTripleWithin_frameL
    ((.x6 ↦ᵣ e3) **
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
     ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3) **
     (.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) ** (.x5 ↦ᵣ tOld) **
     (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
     ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_a2
  have h_oc_a := cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq)
    h_oc_a1 h_a2f
  -- Frame operand_copy's leftovers around the prologue, then sequence.
  have h_prof := cpsTripleWithin_frameL
    ((.x6 ↦ᵣ e3) **
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
     ((evmSp + signExtend12 ((-80) : BitVec 12)) ↦ₘ e2))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_pro
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) h_oc_a h_prof)

/-- Folded post after the headroom entry prefix and final loop-pointer advance.
    The assertion is intentionally still a raw loop-entry surface: later bridge
    lemmas fold it into `expTwoMulFixedFirstIterPreWithResidual` after adding the
    owned scratch/register frame that the entry prefix does not touch. -/
abbrev expHeadroomLoopEntryPost
    (sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word) : Assertion :=
  (.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
  (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
  (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
             + signExtend12 ((-64) : BitVec 12)
             + signExtend12 (64 : BitVec 12))) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
             + signExtend12 (-8 : BitVec 12))) **
  (.x19 ↦ᵣ e3) ** (.x6 ↦ᵣ e3) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
   ((0 : Word) + signExtend12 (1 : BitVec 12))) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
  ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3)

theorem expHeadroomLoopEntryPost_pcFree
    {sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word} :
    (expHeadroomLoopEntryPost sp evmSp b0 b1 b2 b3 e0 e1 e2 e3).pcFree := by
  unfold expHeadroomLoopEntryPost
  pcFree

instance pcFreeInst_expHeadroomLoopEntryPost
    (sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word) :
    Assertion.PCFree
      (expHeadroomLoopEntryPost sp evmSp b0 b1 b2 b3 e0 e1 e2 e3) :=
  ⟨expHeadroomLoopEntryPost_pcFree⟩

/-- The headroom loop-entry post with the concrete `x6` value removed.
    This factors out the one atom that the loop precondition treats as caller
    scratch ownership rather than as a value-bearing register. -/
abbrev expHeadroomLoopEntryPostNoX6
    (sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word) : Assertion :=
  (.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
  (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
  (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
             + signExtend12 ((-64) : BitVec 12)
             + signExtend12 (64 : BitVec 12))) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
             + signExtend12 (-8 : BitVec 12))) **
  (.x19 ↦ᵣ e3) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
   ((0 : Word) + signExtend12 (1 : BitVec 12))) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
  ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3)

abbrev expHeadroomLoopEntryPostOwnX6
    (sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word) : Assertion :=
  regOwn .x6 ** expHeadroomLoopEntryPostNoX6 sp evmSp b0 b1 b2 b3 e0 e1 e2 e3

theorem expHeadroomLoopEntryPostOwnX6_pcFree
    {sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word} :
    (expHeadroomLoopEntryPostOwnX6 sp evmSp b0 b1 b2 b3 e0 e1 e2 e3).pcFree := by
  unfold expHeadroomLoopEntryPostOwnX6 expHeadroomLoopEntryPostNoX6
  pcFree

instance pcFreeInst_expHeadroomLoopEntryPostOwnX6
    (sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word) :
    Assertion.PCFree
      (expHeadroomLoopEntryPostOwnX6 sp evmSp b0 b1 b2 b3 e0 e1 e2 e3) :=
  ⟨expHeadroomLoopEntryPostOwnX6_pcFree⟩

/-- Weaken the concrete `x6` cell in the folded headroom entry post to scratch
    ownership, matching the loop body's first-iteration precondition shape. -/
theorem expHeadroomLoopEntryPost_to_ownX6
    {sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 : Word} {ps : PartialState}
    (h : expHeadroomLoopEntryPost sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 ps) :
    expHeadroomLoopEntryPostOwnX6 sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 ps := by
  unfold expHeadroomLoopEntryPost at h
  unfold expHeadroomLoopEntryPostOwnX6 expHeadroomLoopEntryPostNoX6
  have h_front : ((.x6 ↦ᵣ e3) **
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 (64 : BitVec 12))) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
                  + signExtend12 (-8 : BitVec 12))) **
       (.x19 ↦ᵣ e3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3))) ps := by
    sep_perm h
  exact sepConj_mono_left (regIs_implies_regOwn .x6) _ h_front

/-- Resources that the headroom entry prefix does not produce but that the
    first loop iteration consumes: caller scratch registers, the two temporary
    words above the copied operands, and the untouched live stack tail. -/
abbrev expHeadroomLoopEntryBridgeFrame
    (evmSp v18 vOld : Word) (dWord eWord : EvmWord) (rest : List EvmWord) : Assertion :=
  (.x18 ↦ᵣ v18) ** (.x1 ↦ᵣ vOld) **
  regOwn .x10 ** regOwn .x7 ** regOwn .x11 **
  evmWordIs (evmSp + signExtend12 ((-64) : BitVec 12)) dWord **
  evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) eWord **
  evmStackIs (evmSp + 64) rest

theorem expHeadroomLoopEntryBridgeFrame_pcFree
    {evmSp v18 vOld : Word} {dWord eWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest).pcFree := by
  unfold expHeadroomLoopEntryBridgeFrame
  pcFree

instance pcFreeInst_expHeadroomLoopEntryBridgeFrame
    (evmSp v18 vOld : Word) (dWord eWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest) :=
  ⟨expHeadroomLoopEntryBridgeFrame_pcFree⟩

/-- Fold the headroom entry surface plus the explicit caller/live-stack frame into
    the first fixed-loop iteration precondition with its residual frame. -/
theorem expHeadroomLoopEntryPost_to_firstIterPreWithResidual
    {sp evmSp v18 vOld b0 b1 b2 b3 e0 e1 e2 e3 : Word}
    {dWord eWord : EvmWord} {rest : List EvmWord} {ps : PartialState}
    (h : (expHeadroomLoopEntryPost sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 **
          expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest) ps) :
    expTwoMulFixedFirstIterPreWithResidual sp
      (evmSp + signExtend12 ((-128) : BitVec 12)) v18 vOld
      (expResultWord b0 b1 b2 b3) (expResultWord e0 e1 e2 e3)
      dWord eWord
      (expResultWord b0 b1 b2 b3 :: expResultWord e0 e1 e2 e3 :: rest) ps := by
  obtain ⟨psPost, psFrame, h_disjoint, h_union, hPost, hFrame⟩ := h
  have hPostOwn := expHeadroomLoopEntryPost_to_ownX6 hPost
  have hOwnFrame :
      (expHeadroomLoopEntryPostOwnX6 sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 **
       expHeadroomLoopEntryBridgeFrame evmSp v18 vOld dWord eWord rest) ps :=
    ⟨psPost, psFrame, h_disjoint, h_union, hPostOwn, hFrame⟩
  rw [expTwoMulFixedFirstIterPreWithResidual]
  apply expTwoMulFixedFirstIterPreOwned_choose_frame
  rw [expTwoMulFixedFirstIterPreOwned_unfold,
    expTwoMulFixedFirstIterEntryResidual_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  unfold expHeadroomLoopEntryPostOwnX6 expHeadroomLoopEntryPostNoX6
    expHeadroomLoopEntryBridgeFrame at hOwnFrame
  unfold evmWordIs at hOwnFrame
  unfold evmWordIs evmStackIs
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    signExtend12_64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    EvmWord.getLimbN_one_zero, EvmWord.getLimbN_one_one,
    EvmWord.getLimbN_one_two, EvmWord.getLimbN_one_three,
    expResultWord_getLimbN_0, expResultWord_getLimbN_1,
    expResultWord_getLimbN_2, expResultWord_getLimbN_3,
    show ((0 : Word) + signExtend12 (256 : BitVec 12)) = (256 : Word) from by decide,
    show ((0 : Word) + signExtend12 (1 : BitVec 12)) = (1 : Word) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 8 : Word) = signExtend12 ((-120) : BitVec 12) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 16 : Word) = signExtend12 ((-112) : BitVec 12) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 24 : Word) = signExtend12 ((-104) : BitVec 12) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 32 : Word) = signExtend12 ((-96) : BitVec 12) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 40 : Word) = signExtend12 ((-88) : BitVec 12) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 56 : Word) = signExtend12 ((-72) : BitVec 12) from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 64 : Word) = 18446744073709551552 from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 96 : Word) = 18446744073709551584 from by decide,
    show (signExtend12 ((-128) : BitVec 12) + 128 : Word) = 0 from by decide,
    show (signExtend12 ((-72) : BitVec 12) + signExtend12 ((-8) : BitVec 12) : Word) = signExtend12 ((-80) : BitVec 12) from by decide,
    show (18446744073709551552 + (18446744073709551552 + 64) : Word) = 18446744073709551552 from by decide,
    show (18446744073709551552 + 8 : Word) = 18446744073709551560 from by decide,
    show (18446744073709551552 + 16 : Word) = 18446744073709551568 from by decide,
    show (18446744073709551552 + 24 : Word) = 18446744073709551576 from by decide,
    show (18446744073709551584 + 8 : Word) = 18446744073709551592 from by decide,
    show (18446744073709551584 + 16 : Word) = 18446744073709551600 from by decide,
    show (18446744073709551584 + 24 : Word) = 18446744073709551608 from by decide,
    BitVec.add_assoc] at hOwnFrame ⊢
  unfold evmStackIs
  unfold evmWordIs
  simp only [expResultWord_getLimbN_0, expResultWord_getLimbN_1,
    expResultWord_getLimbN_2, expResultWord_getLimbN_3,
    show (evmSp + 32 + 8 : Word) = evmSp + 40 from by bv_omega,
    show (evmSp + 32 + 16 : Word) = evmSp + 48 from by bv_omega,
    show (evmSp + 32 + 24 : Word) = evmSp + 56 from by bv_omega,
    show (evmSp + 32 + 32 : Word) = evmSp + 64 from by bv_omega] at hOwnFrame ⊢
  xperm_hyp hOwnFrame

/-- `entry_prefix ;; loop_advance(+64)` (base+0 → base+116): the entry prefix walks
    `x12` down to `evmSp-128` and inits the accumulator; the loop-advance then bumps
    `x12` to `(evmSp-64-64)+64 = evmSp_iter`, exactly the IterPre coordinate of the
    body-only loop instantiated at `evmSp_param = evmSp-64-64`. -/
theorem exp_headroom_entry_to_loopadvance_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    cpsTripleWithin 29 base (base + 116)
      (evm_exp_headroom_code squaringMulOff condMulOff skipOff backOff base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
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
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 (64 : BitVec 12))) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
                  + signExtend12 (-8 : BitVec 12))) **
       (.x19 ↦ᵣ e3) ** (.x6 ↦ᵣ e3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
  have h_ep := exp_headroom_entry_prefix_spec_within sp evmSp cOld tOld c6Old c16Old
    c19Old m0 m1 m2 m3 v6 b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
    squaringMulOff condMulOff skipOff backOff
  have h_la := exp_headroom_loop_advance_lifted
    (evmSp + signExtend12 ((-64) : BitVec 12) + signExtend12 ((-64) : BitVec 12))
    base squaringMulOff condMulOff skipOff backOff
  have h_laf := cpsTripleWithin_frameL
    ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
     (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
     (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
     (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
                + signExtend12 (-8 : BitVec 12))) **
     (.x19 ↦ᵣ e3) ** (.x6 ↦ᵣ e3) **
     ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
      ((0 : Word) + signExtend12 (1 : BitVec 12))) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
     ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    h_la
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hq => by xperm_hyp hq) h_ep h_laf)

theorem exp_headroom_entry_to_loopadvance_canonical_appended_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word) :
    cpsTripleWithin 29 base (base + 116)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
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
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 (64 : BitVec 12))) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
                  + signExtend12 (-8 : BitVec 12))) **
       (.x19 ↦ᵣ e3) ** (.x6 ↦ᵣ e3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
  have h := exp_headroom_entry_to_loopadvance_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
  refine cpsTripleWithin_extend_code ?_ h
  intro a i ha
  exact CodeReq.union_mono_left a i ha

theorem exp_headroom_entry_to_loopadvance_canonical_appended_folded
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word) :
    cpsTripleWithin 29 base (base + 116)
      (evm_exp_headroom_canonical_appended_mul_code base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
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
      (expHeadroomLoopEntryPost sp evmSp b0 b1 b2 b3 e0 e1 e2 e3) := by
  unfold expHeadroomLoopEntryPost
  exact exp_headroom_entry_to_loopadvance_canonical_appended_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
    b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base

/-- Framed folded-post variant of the canonical appended-code entry prefix. -/
theorem exp_headroom_entry_to_loopadvance_canonical_appended_folded_framed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 29 base (base + 116)
      (evm_exp_headroom_canonical_appended_mul_code base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
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
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) ** F)
      (expHeadroomLoopEntryPost sp evmSp b0 b1 b2 b3 e0 e1 e2 e3 ** F) :=
  cpsTripleWithin_frameR F hF
    (exp_headroom_entry_to_loopadvance_canonical_appended_folded
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base)

/-- Framed canonical appended-code entry prefix, for carrying headroom scratch
    resources into the loop precondition bridge. -/
theorem exp_headroom_entry_to_loopadvance_canonical_appended_framed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 29 base (base + 116)
      (evm_exp_headroom_canonical_appended_mul_code base)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (.x12 ↦ᵣ evmSp) ** (.x6 ↦ᵣ v6) **
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
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ h7)) ** F)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 ((-64) : BitVec 12)
                  + signExtend12 (64 : BitVec 12))) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x16 ↦ᵣ (evmSp + signExtend12 ((-72) : BitVec 12)
                  + signExtend12 (-8 : BitVec 12))) **
       (.x19 ↦ᵣ e3) ** (.x6 ↦ᵣ e3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
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
       ((evmSp + signExtend12 ((-72) : BitVec 12)) ↦ₘ e3)) ** F) :=
  cpsTripleWithin_frameR F hF
    (exp_headroom_entry_to_loopadvance_canonical_appended_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 v6
      b0 b1 b2 b3 e0 e1 e2 e3 h0 h1 h2 h3 h4 h5 h6 h7 base)



end EvmAsm.Evm64.Exp.Compose
