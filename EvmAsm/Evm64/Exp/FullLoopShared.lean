/-
  Shared declaration home for the saved-bit full-loop prefix, squaring, and branch stages.
-/

import EvmAsm.Evm64.Exp.SavedBitWithMulLoopShared
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- MSB bit-test block lifted to the corrected saved-bit EXP+MUL code bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_msb_bit_test_evm_exp_msb_saved_bit_spec_within
      e c v10 mulOff skipOff backOff base)

/-- MSB bit-test block lifted to the two-MUL-offset saved-bit EXP+MUL bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c v10 : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) := by
  have h := EvmAsm.Evm64.exp_msb_bit_test_block_spec_within e c v10 (base + 28)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterBitTestNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := fun a i hi =>
      evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (evmExpMsbSavedBitTwoMulCode_iter_body_sub
          (base := base) (squaringMulOff := squaringMulOff)
          (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
          a i (expIterBodyFullMsbSavedBitTwoMulCode_bit_test_sub a i hi)))

/-- Save-bit block lifted to the corrected saved-bit EXP+MUL code bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    (bit v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_save_bit_evm_exp_msb_saved_bit_spec_within
      bit v18 mulOff skipOff backOff base)

/-- Save-bit block lifted to the two-MUL-offset saved-bit EXP+MUL bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (bit v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_save_bit_block_spec_within bit v18 (base + 40)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSavedBitSaveNextPc] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := fun a i hi => by
      rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitSaveEntryAddr] at hi
      exact evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (evmExpMsbSavedBitTwoMulCode_iter_body_sub
          (base := base) (squaringMulOff := squaringMulOff)
          (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
          a i (expIterBodyFullMsbSavedBitTwoMulCode_save_bit_sub a i hi)))

/-- Prefix of one corrected EXP iteration: extract the current MSB into `x10`
    and save the same bit in callee-saved `x18` before the squaring call. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let bit := expTwoMulIterBit e
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit
  have hBit := exp_msb_bit_test_evm_exp_msb_saved_bit_with_mul_spec_within
    e c v10 mulOff skipOff backOff base mulTarget
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave := exp_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    bit v18 mulOff skipOff backOff base mulTarget
  have hSaveFramed :=
    cpsTripleWithin_frameL
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))))
      (by pcFree) hSave
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Two-MUL-offset prefix of one corrected EXP iteration: extract the current
    MSB into `x10` and save the same bit in `x18` before the squaring call. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c v10 v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    let bit := expTwoMulIterBit e
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit
  have hBit := exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 squaringMulOff condMulOff skipOff backOff base mulTarget
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave := exp_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    bit v18 squaringMulOff condMulOff skipOff backOff base mulTarget
  have hSaveFramed :=
    cpsTripleWithin_frameL
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))))
      (by pcFree) hSave
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the corrected
    saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base mulTarget target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  cpsBranchWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_spec_within
      mulOff skipOff backOff v18 base target htarget)

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the two-MUL-offset
    saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base mulTarget target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x18 .x0 skipOff v18 (0 : Word)
    (base + 148)
  rw [htarget] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSavedBitCondMulBeqNextPc] at h
  exact cpsBranchWithin_extend_code
    (h := h)
    (hmono := fun a i hi => by
      rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitCondMulBeqEntryAddr] at hi
      exact evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (evmExpMsbSavedBitTwoMulCode_iter_body_sub
          (base := base) (squaringMulOff := squaringMulOff)
          (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
          a i (expIterBodyFullMsbSavedBitTwoMulCode_cond_mul_sub a i
            (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
              ((base + 28) + 120) condMulOff skipOff a i hi))))

/-- Saved-bit loop-back block lifted directly to the corrected EXP+MUL code
    bundle. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 256) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 264)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 256)
    target htarget
  rw [expTopSavedBitLoopBackNextPc] at h
  simpa [expIterCountNew] using
    (cpsBranchWithin_extend_code (h := h)
      (hmono := fun a i hi =>
        evmExpMsbSavedBitWithMulCode_exp_sub a i
          (evmExpMsbSavedBitCode_iter_loop_back_sub a i hi)))

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Squaring-side full call-block lifted to the corrected saved-bit EXP+MUL
    code bundle.  The block starts after the saved-bit instruction, at
    `base + 44`, and exits at the saved-bit BEQ site `base + 148`. -/
theorem exp_squaring_call_block_evm_exp_msb_saved_bit_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) (base + 44) ((base + 44) + 104)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro squareW
  have hbase' : (base + 44 : Word) &&& 1 = 0 :=
    EvmAsm.Evm64.Exp.AddrNorm.expBaseAdd44Aligned base hbase
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 44) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_squaring_call_block_code (base + 44) mulOff a with
      | none => rfl
      | some i =>
        have hev := evmExpMsbSavedBitCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_squaring_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 44) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitWithMulCode_exp_sub a i
        (evmExpMsbSavedBitCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i h))
      (fun a i h => evmExpMsbSavedBitWithMulCode_mul_sub hd a i h))
    hbase_spec

/-- Squaring-side call-block lifted to the two-MUL-offset saved-bit EXP+MUL
    code bundle.  This uses the squaring JAL offset only; the conditional
    multiply offset is independent. -/
theorem exp_squaring_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) (base + 44) ((base + 44) + 104)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro squareW
  have hbase' : (base + 44 : Word) &&& 1 = 0 :=
    EvmAsm.Evm64.Exp.AddrNorm.expBaseAdd44Aligned base hbase
  have hSquareSub : ∀ a i,
      exp_squaring_call_block_code (base + 44) squaringMulOff a = some i →
      evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff a = some i := by
    intro a i h
    rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitSquaringEntryAddr] at h
    exact evmExpMsbSavedBitTwoMulCode_iter_body_sub
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
      a i (expIterBodyFullMsbSavedBitTwoMulCode_squaring_sub a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 44) squaringMulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_squaring_call_block_code (base + 44) squaringMulOff a with
      | none => rfl
      | some i =>
        have hev := hSquareSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_squaring_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget squaringMulOff (base + 44)
    hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (hSquareSub a i h))
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_mul_sub hd a i h))
    hbase_spec

/-- Prefix plus squaring side of one corrected EXP iteration.  This carries
    the saved bit in `x18` across the full `mul_callable` round-trip, landing
    at the saved-bit conditional-multiply BEQ site. -/
theorem exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) (base + 148)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro bit squareW
  have hPrefix := exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    e c v10 v18 mulOff skipOff backOff base mulTarget
  have hPrefixFramed :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)
      ) (by pcFree) hPrefix
  have hSquare := exp_squaring_call_block_evm_exp_msb_saved_bit_with_mul_spec_within
    sp evmSp (e <<< (1 : BitVec 6).toNat) vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    (c + signExtend12 ((-1) : BitVec 12)) v7 bit v11 mulTarget
    mulOff skipOff backOff base hbase hmt hd
  have hSquareFramed :=
    cpsTripleWithin_frameL (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))
      (by pcFree) hSquare
  have hSeq :
      cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) ((base + 44) + 104)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp only [bit] at hp ⊢
        xperm_hyp hp)
      hPrefixFramed hSquareFramed
  rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitSquaringPrefixExitPc] at hSeq
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Two-MUL-offset prefix plus squaring side of one corrected EXP iteration.
    The saved bit in `x18` is carried across the squaring `mul_callable`
    round-trip, landing at the saved-bit BEQ site. -/
theorem exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) (base + 148)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro bit squareW
  have hPrefix :=
    exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c v10 v18 squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPrefixFramed :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) (by pcFree) hPrefix
  have hSquare :=
    exp_squaring_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp (e <<< (1 : BitVec 6).toNat) vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      (c + signExtend12 ((-1) : BitVec 12)) v7 bit v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base hbase hmt hd
  have hSquareFramed :=
    cpsTripleWithin_frameL (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))
      (by pcFree) hSquare
  have hSeq :
      cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) ((base + 44) + 104)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp only [bit] at hp ⊢
        xperm_hyp hp)
      hPrefixFramed hSquareFramed
  rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitSquaringPrefixExitPc] at hSeq
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

@[irreducible]
def expTwoMulSkipLoopRest
    (bit sp evmSp base : Word) (squareW : EvmWord) : Assertion :=
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ squareW.getLimbN 3) **
  evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ ((base + 44) + 68))

theorem expTwoMulSkipLoopRest_unfold
    {bit sp evmSp base : Word} {squareW : EvmWord} :
    expTwoMulSkipLoopRest bit sp evmSp base squareW =
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  delta expTwoMulSkipLoopRest
  rfl

theorem expTwoMulSkipLoopRest_pcFree
    {bit sp evmSp base : Word} {squareW : EvmWord} :
    (expTwoMulSkipLoopRest bit sp evmSp base squareW).pcFree := by
  rw [expTwoMulSkipLoopRest_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  pcFree

/-- Bundles `expTwoMulSkipLoopRest` with the `bit` and `squareW` computations
    so skip specs need only two statement lets instead of three. -/
@[irreducible]
def expTwoMulSkipIterRest
    (e sp evmSp base r0 r1 r2 r3 : Word) : Assertion :=
  expTwoMulSkipLoopRest
    (expTwoMulIterBit e) sp evmSp base (expTwoMulSquareW r0 r1 r2 r3)

theorem expTwoMulSkipIterRest_unfold
    {e sp evmSp base r0 r1 r2 r3 : Word} :
    expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3 =
      expTwoMulSkipLoopRest
        (expTwoMulIterBit e) sp evmSp base (expTwoMulSquareW r0 r1 r2 r3) := by
  delta expTwoMulSkipIterRest; rfl

/-- Two-MUL-offset prefix plus squaring side followed by the saved-bit BEQ.
    This is the branch handoff immediately before optional conditional
    multiply under the fixed two-offset layout. -/
theorem exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ squareW.getLimbN 3) **
         evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68)))
      (base + 152)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ squareW.getLimbN 3) **
         evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro bit squareW
  let rest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ ((base + 44) + 68))
  have hPrefixSquare :=
    exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget squaringMulOff condMulOff skipOff backOff base
      hbase hmt hd
  have hPrefixSquareFramed :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) hPrefixSquare
  have hBeq := exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    squaringMulOff condMulOff skipOff backOff
    (bit + signExtend12 (0 : BitVec 12)) base mulTarget target htarget
  have hBeqFramed := cpsBranchWithin_frameR rest (by
    dsimp [rest]
    pcFree) hBeq
  have hSeq :
      cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        _ target _ (base + 152) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, bit] at hp ⊢
        xperm_hyp hp)
      hPrefixSquareFramed hBeqFramed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    hSeq

/-- Prefix plus squaring side followed by the saved-bit BEQ.  This is the
    branch handoff immediately before the optional conditional multiply. -/
theorem exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base target : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ squareW.getLimbN 3) **
         evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68)))
      (base + 152)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ squareW.getLimbN 3) **
         evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro bit squareW
  let rest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ ((base + 44) + 68))
  have hPrefixSquare :=
    exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget mulOff skipOff backOff base hbase hmt hd
  have hPrefixSquareFramed :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) hPrefixSquare
  have hBeq := exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    mulOff skipOff backOff (bit + signExtend12 (0 : BitVec 12))
    base mulTarget target htarget
  have hBeqFramed := cpsBranchWithin_frameR rest (by
    dsimp [rest]
    pcFree) hBeq
  have hSeq :
      cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        _ target _ (base + 152) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, bit] at hp ⊢
        xperm_hyp hp)
      hPrefixSquareFramed hBeqFramed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    hSeq

/-- Zero-bit path through the saved-bit BEQ, followed by the loop-back
    counter update.  The nonzero conditional-multiply path is left as the
    first exit for the next composition slice. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
      [((base + 152),
          ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)),
        (loopTarget,
          (((.x9 ↦ᵣ expIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3)),
        (base + 264,
          (((.x9 ↦ᵣ expIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3))] := by
  intro bit squareW
  have hBranch :=
    exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget mulOff skipOff backOff base (base + 256)
      hbase hmt hd hskip
  have hBranchFramed :=
    cpsBranchWithin_frameR (.x9 ↦ᵣ iterCount) (by pcFree) hBranch
  have hBranchSwapped := cpsBranchWithin_swap hBranchFramed
  have hLoop := exp_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within
    iterCount mulOff skipOff backOff base mulTarget loopTarget hback
  have hLoopFramed := cpsBranchWithin_frameR (expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) (by
    simp only [expTwoMulSkipIterRest_unfold]
    exact expTwoMulSkipLoopRest_pcFree) hLoop
  have hLoopN := cpsBranchWithin_as_cpsNBranchWithin hLoopFramed
  have hSeq :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        _ _ :=
    cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr
      (fun _ hp => by
        simp [expTwoMulSkipIterRest_unfold, expTwoMulSkipLoopRest_unfold,
              expTwoMulIterBit] at hp ⊢
        xperm_hyp hp)
      hBranchSwapped hLoopN
  have hSeqPre :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
         ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
         ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
         ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
         ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
         ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
         ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
         ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
         ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
         (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
        _ :=
    cpsNBranchWithin_weaken_pre
      (fun _ hp => by xperm_hyp hp) hSeq
  exact hSeqPre

/-- Bundled base-operand window assertion (evmSp[-64..-40]). Used in the
    `with_base_frame` variants of the saved-bit skip-path to carry the second
    multiplicand limbs across the loop body. Marked `@[irreducible]` to keep
    it opaque in spec statements. -/
@[irreducible]
def expTwoMulBaseFrame (evmSp a0 a1 a2 a3 : Word) : Assertion :=
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)

theorem expTwoMulBaseFrame_unfold {evmSp a0 a1 a2 a3 : Word} :
    expTwoMulBaseFrame evmSp a0 a1 a2 a3 =
      (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  delta expTwoMulBaseFrame; rfl

theorem expTwoMulBaseFrame_pcFree {evmSp a0 a1 a2 a3 : Word} :
    (expTwoMulBaseFrame evmSp a0 a1 a2 a3).pcFree := by
  rw [expTwoMulBaseFrame_unfold]; pcFree

/-- Frame-preserving variant of the zero-bit skip path that carries the saved
    base operand window needed by the conditional-multiply handoff. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_with_base_frame_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) **
        expTwoMulBaseFrame evmSp a0 a1 a2 a3)
      [((base + 152),
          (((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)) **
          expTwoMulBaseFrame evmSp a0 a1 a2 a3),
        (loopTarget,
          ((((.x9 ↦ᵣ expIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
            expTwoMulBaseFrame evmSp a0 a1 a2 a3)),
        (base + 264,
          ((((.x9 ↦ᵣ expIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
            expTwoMulBaseFrame evmSp a0 a1 a2 a3))] := by
  intro bit squareW
  have h :=
    exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget mulOff skipOff backOff base loopTarget
      hbase hmt hd hskip hback
  have hf := cpsNBranchWithin_frameR (F := expTwoMulBaseFrame evmSp a0 a1 a2 a3)
    expTwoMulBaseFrame_pcFree h
  simpa [expTwoMulBaseFrame_unfold, expTwoMulSkipIterRest_unfold,
         expTwoMulSkipLoopRest_unfold] using
    (cpsNBranchWithin_weaken_pre
      (fun _ hp => by simpa [expTwoMulBaseFrame_unfold] using hp) hf)

end EvmAsm.Evm64.Exp.Compose
