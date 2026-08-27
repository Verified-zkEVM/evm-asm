/-
  EvmAsm.Evm64.Exp.Compose.TopBoundaryBlocks

  Boundary block specs lifted to the top-level EXP code bundles.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBase
public import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
public import EvmAsm.Evm64.Exp.AddrNorm

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Pointer advance lifted to the top-level EXP code bundle. -/
theorem exp_loop_pointer_advance_evm_exp_spec_within
    (vOld : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 24) (base + 28)
      (evmExpCode base mulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_advance_spec_within vOld (base + 24)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopPointerAdvanceNextPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_pointer_advance_sub)

/-- Pointer restore lifted to the top-level EXP code bundle. -/
theorem exp_loop_pointer_restore_evm_exp_spec_within
    (vOld : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 260) (base + 264)
      (evmExpCode base mulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_restore_spec_within vOld (base + 260)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopPointerRestoreNextPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_pointer_restore_sub)

/-- EXP prologue lifted to the top-level EXP code bundle. -/
theorem exp_prologue_evm_exp_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 6 base (base + 24)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord)) := by
  have h := EvmAsm.Evm64.exp_prologue_word_spec_within
    sp cOld tOld m0 m1 m2 m3 base
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_prologue_sub)

/-- EXP epilogue lifted to the top-level EXP code bundle. -/
theorem exp_epilogue_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 264) (base + 300)
      (evmExpCode base mulOff skipOff backOff)
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
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  have h := EvmAsm.Evm64.exp_epilogue_word_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 264)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopEpilogueNextPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_epilogue_sub)

/-- Pointer advance lifted to the two-MUL saved-bit top-level EXP code
    bundle. -/
theorem exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base : Word) :
    cpsTripleWithin 1 (base + 24) (base + 28)
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 (64 : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_advance_spec_within vOld (base + 24)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopPointerAdvanceNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := evmExpMsbSavedBitTwoMulCode_pointer_advance_sub)

/-- Pointer restore lifted to the two-MUL saved-bit top-level EXP code
    bundle. -/
theorem exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base : Word) :
    cpsTripleWithin 1 (base + 264) (base + 268)
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_restore_spec_within vOld (base + 264)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSavedBitEpilogueEntryNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := evmExpMsbSavedBitTwoMulCode_pointer_restore_sub)

/-- EXP prologue lifted to the two-MUL saved-bit top-level EXP code bundle. -/
theorem exp_prologue_evm_exp_msb_saved_bit_two_mul_spec_within
    (sp cOld tOld m0 m1 m2 m3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 6 base (base + 24)
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord)) := by
  have h := EvmAsm.Evm64.exp_prologue_word_spec_within
    sp cOld tOld m0 m1 m2 m3 base
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := evmExpMsbSavedBitTwoMulCode_prologue_sub)

/-- EXP epilogue lifted to the two-MUL saved-bit top-level EXP code bundle. -/
theorem exp_epilogue_evm_exp_msb_saved_bit_two_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 268) (base + 304)
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
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
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  have h := EvmAsm.Evm64.exp_epilogue_word_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 268)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSavedBitEpilogueNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := evmExpMsbSavedBitTwoMulCode_epilogue_sub)

end EvmAsm.Evm64.Exp.Compose
