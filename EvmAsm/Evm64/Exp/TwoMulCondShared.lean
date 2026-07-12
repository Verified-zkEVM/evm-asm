/-
  Shared declaration home for saved-bit conditional multiplication, skip, and two-mul conditions.
-/

import EvmAsm.Evm64.Exp.FullLoopShared
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Conditional-multiply taken call-block lifted to the corrected saved-bit
    EXP+MUL code bundle.  The leading BEQ is handled separately; this theorem
    starts at the taken block `base + 152` and exits at `base + 256`. -/
theorem exp_cond_mul_call_block_evm_exp_msb_saved_bit_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 152) ((base + 152) + 104)
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
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (r * aw).getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp (r * aw) ** evmWordIs (evmSp + 32) (r * aw) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 152) + 68))) := by
  intro r aw
  have hbase' : (base + 152 : Word) &&& 1 = 0 :=
    EvmAsm.Evm64.Exp.AddrNorm.expBaseAdd152Aligned base hbase
  have hCondSub : ∀ a i,
      exp_cond_mul_call_block_code (base + 152) mulOff a = some i →
      evmExpMsbSavedBitCode base mulOff skipOff backOff a = some i := by
    intro a i h
    rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitCondMulTakenAddr] at h
    exact evmExpMsbSavedBitCode_iter_cond_mul_sub a i
      (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_call_sub
        (base + 148) mulOff skipOff a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 152) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 152) mulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 152) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitWithMulCode_exp_sub a i (hCondSub a i h))
      (fun a i h => evmExpMsbSavedBitWithMulCode_mul_sub hd a i h))
    hbase_spec

/-- Conditional-multiply taken call-block lifted to the two-MUL-offset
    saved-bit EXP+MUL code bundle.  This uses the conditional-multiply JAL
    offset only; the squaring offset is independent. -/
theorem exp_cond_mul_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 152) ((base + 152) + 104)
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
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (r * aw).getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp (r * aw) ** evmWordIs (evmSp + 32) (r * aw) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 152) + 68))) := by
  intro r aw
  have hbase' : (base + 152 : Word) &&& 1 = 0 :=
    EvmAsm.Evm64.Exp.AddrNorm.expBaseAdd152Aligned base hbase
  have hCondSub : ∀ a i,
      exp_cond_mul_call_block_code (base + 152) condMulOff a = some i →
      evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff a = some i := by
    intro a i h
    rw [EvmAsm.Evm64.Exp.AddrNorm.expSavedBitTwoMulCondMulTakenAddr] at h
    exact evmExpMsbSavedBitTwoMulCode_iter_body_sub
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
      a i (expIterBodyFullMsbSavedBitTwoMulCode_cond_mul_sub a i
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_call_sub
          ((base + 28) + 120) condMulOff skipOff a i h))
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 152) condMulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 152) condMulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget condMulOff (base + 152) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (hCondSub a i h))
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_mul_sub hd a i h))
    hbase_spec

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Saved-bit loop-back block lifted to the two-MUL-offset EXP+MUL code
    bundle. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (c : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 256) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c ≠ 0⌝)
      (base + 264)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 256)
    target htarget
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTwoMulSkipLoopBackNextPc] at h
  simpa [expTwoMulIterCountNew] using
    (cpsBranchWithin_extend_code (h := h)
      (hmono := fun a i hi =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
          (evmExpMsbSavedBitTwoMulCode_iter_loop_back_sub a i hi)))

/-- Zero-bit path through the two-MUL-offset saved-bit BEQ, followed by the
    loop-back counter update.  The nonzero conditional-multiply path is left
    as the first exit for the next composition slice. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
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
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3))] := by
  intro bit squareW
  have hBranch :=
    exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget squaringMulOff condMulOff skipOff backOff base
      (base + 256) hbase hmt hd hskip
  have hBranchFramed :=
    cpsBranchWithin_frameR (.x9 ↦ᵣ iterCount) (by pcFree) hBranch
  have hBranchSwapped := cpsBranchWithin_swap hBranchFramed
  have hLoop := exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base mulTarget
    loopTarget hback
  have hLoopFramed := cpsBranchWithin_frameR
    (expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) (by
      rw [expTwoMulSkipIterRest_unfold]
      exact expTwoMulSkipLoopRest_pcFree) hLoop
  have hLoopN := cpsBranchWithin_as_cpsNBranchWithin hLoopFramed
  have hSeq :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        _ _ :=
    cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr
      (fun _ hp => by
        simp [expTwoMulSkipIterRest_unfold, expTwoMulSkipLoopRest_unfold] at hp ⊢
        xperm_hyp hp)
      hBranchSwapped hLoopN
  have hSeqPre :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
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
         (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
        _ :=
    cpsNBranchWithin_weaken_pre
      (fun _ hp => by xperm_hyp hp) hSeq
  exact hSeqPre

/-- Frame-preserving two-MUL-offset variant of the zero-bit skip path that
    carries the saved base operand window needed by the conditional-multiply
    handoff. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_with_base_frame_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
            expTwoMulBaseFrame evmSp a0 a1 a2 a3)),
        (base + 264,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
            expTwoMulBaseFrame evmSp a0 a1 a2 a3))] := by
  intro bit squareW
  have h :=
    exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget squaringMulOff condMulOff skipOff
      backOff base loopTarget hbase hmt hd hskip hback
  have hf := cpsNBranchWithin_frameR (F := expTwoMulBaseFrame evmSp a0 a1 a2 a3)
    expTwoMulBaseFrame_pcFree h
  simpa [expTwoMulBaseFrame_unfold, expTwoMulSkipIterRest_unfold,
         expTwoMulSkipLoopRest_unfold] using
    (cpsNBranchWithin_weaken_pre
      (fun _ hp => by simpa [expTwoMulBaseFrame_unfold] using hp) hf)

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

@[irreducible]
def expCondMulLoopRest
    (sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord) : Assertion :=
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ rw.getLimbN 3) **
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
  evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ ((base + 152) + 68))

theorem expCondMulLoopRest_unfold
    {sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord} :
    expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw =
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ rw.getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 152) + 68))) := by
  delta expCondMulLoopRest
  rfl

theorem expCondMulLoopRest_pcFree
    {sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord} :
    (expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw).pcFree := by
  rw [expCondMulLoopRest_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  pcFree

/-- Taken conditional-multiply block followed by the loop-back counter update
    under the two-MUL-offset saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulCondRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
       (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word)))
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] := by
  intro rw
  have hCond :=
    exp_cond_mul_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base hbase hmt hd
  have hCondFramed :=
    cpsTripleWithin_frameR
      ((.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hCond
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTwoMulCondMulCallExitPc] at hCondFramed
  have hLoop := exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base mulTarget
    loopTarget hback
  have hLoopFramed :=
    cpsBranchWithin_frameR
      (expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)
      expCondMulLoopRest_pcFree hLoop
  have hSeq :
      cpsBranchWithin ((17 + 64 + 9) + 2) (base + 152)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        _ loopTarget _ (base + 264) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        rw [expCondMulLoopRest_unfold]
        dsimp [rw] at hp ⊢
        xperm_hyp hp)
      hCondFramed hLoopFramed
  have hSeqN := cpsBranchWithin_as_cpsNBranchWithin hSeq
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hSeqN

/-- Variant of the conditional-multiply path that consumes owned caller-saved
    call scratch in the precondition. The data words stay in the concrete
    limb form expected by the base theorem; only the overwritten registers and
    memory cells are existentially owned. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_call_scratch_owned_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3
      e0 e1 e2 e3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulCondRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (preCore **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] := by
  intro rw preCore
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x6)
    (P := preCore ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v6
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x7)
    (P := preCore ** (.x6 ↦ᵣ v6) ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v7
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x10)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v10
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x11)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v11
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      memOwn (evmSp + 8) ** memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d0
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 8)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d1
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 16)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      ((evmSp + 8) ↦ₘ d1) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d2
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 24)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      ((evmSp + 8) ↦ₘ d1) ** ((evmSp + 16) ↦ₘ d2))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d3
  have hConcrete :=
    exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base loopTarget hbase hmt hd hback
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [preCore] at hp ⊢
      have hSp0 : (sp + signExtend12 0#12 : Word) = sp := EvmAsm.Evm64.Exp.AddrNorm.expAddr0 sp
      have hSp8 : (sp + signExtend12 8#12 : Word) = sp + 8 := EvmAsm.Evm64.Exp.AddrNorm.expAddr8 sp
      have hSp16 : (sp + signExtend12 16#12 : Word) = sp + 16 := EvmAsm.Evm64.Exp.AddrNorm.expAddr16 sp
      have hSp24 : (sp + signExtend12 24#12 : Word) = sp + 24 := EvmAsm.Evm64.Exp.AddrNorm.expAddr24 sp
      have hEvm0 : (evmSp + signExtend12 0#12 : Word) = evmSp := EvmAsm.Evm64.Exp.AddrNorm.expAddr0 evmSp
      have hEvm8 : (evmSp + signExtend12 8#12 : Word) = evmSp + 8#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr8 evmSp
      have hEvm16 : (evmSp + signExtend12 16#12 : Word) = evmSp + 16#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr16 evmSp
      have hEvm24 : (evmSp + signExtend12 24#12 : Word) = evmSp + 24#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr24 evmSp
      have hEvm32 : (evmSp + signExtend12 32#12 : Word) = evmSp + 32 := EvmAsm.Evm64.Exp.AddrNorm.expAddr32 evmSp
      have hEvm40 : (evmSp + signExtend12 40#12 : Word) = evmSp + 40 := EvmAsm.Evm64.Exp.AddrNorm.expAddr40 evmSp
      have hEvm48 : (evmSp + signExtend12 48#12 : Word) = evmSp + 48 := EvmAsm.Evm64.Exp.AddrNorm.expAddr48 evmSp
      have hEvm56 : (evmSp + signExtend12 56#12 : Word) = evmSp + 56 := EvmAsm.Evm64.Exp.AddrNorm.expAddr56 evmSp
      rw [hSp0, hSp8, hSp16, hSp24, hEvm32, hEvm40, hEvm48, hEvm56] at hp ⊢
      rw [hEvm0, hEvm8, hEvm16, hEvm24]
      xperm_hyp hp)
    hConcrete

/-- Assertion-level bridge from the folded-word precondition produced by the
    two-MUL saved-bit prefix to the concrete-limb precondition consumed by the
    conditional-multiply adapter. Keeping this as a pure assertion implication
    avoids comparing the full generated CPS theorem type while still isolating
    the `evmWordIs` unfolding and address normalization needed by the next
    composition slice. -/
theorem exp_cond_mul_folded_pre_to_call_scratch_owned_pre
    (sp evmSp iterCount vOld a0 a1 a2 a3 : Word) (r : EvmWord) :
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let foldedPre : Assertion :=
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
        evmWordIs sp r ** evmWordIs (evmSp + 32) r **
        baseFrame ** (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
        (.x0 ↦ᵣ (0 : Word))) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    let concretePre : Assertion :=
      let preCore : Assertion :=
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r.getLimbN 0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r.getLimbN 1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r.getLimbN 2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r.getLimbN 3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r.getLimbN 0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r.getLimbN 1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r.getLimbN 2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r.getLimbN 3) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
      preCore **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24)
    ∀ h, foldedPre h → concretePre h := by
  intro baseFrame foldedPre concretePre h hp
  dsimp [foldedPre, concretePre, baseFrame] at hp ⊢
  unfold evmWordIs at hp
  rw [EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add8,
    EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add16,
    EvmAsm.Evm64.Exp.AddrNorm.expAdd32Add24] at hp
  have hSp0 : (sp + signExtend12 0#12 : Word) = sp := EvmAsm.Evm64.Exp.AddrNorm.expAddr0 sp
  have hSp8 : (sp + signExtend12 8#12 : Word) = sp + 8 := EvmAsm.Evm64.Exp.AddrNorm.expAddr8 sp
  have hSp16 : (sp + signExtend12 16#12 : Word) = sp + 16 := EvmAsm.Evm64.Exp.AddrNorm.expAddr16 sp
  have hSp24 : (sp + signExtend12 24#12 : Word) = sp + 24 := EvmAsm.Evm64.Exp.AddrNorm.expAddr24 sp
  have hEvm32 : (evmSp + signExtend12 32#12 : Word) = evmSp + 32#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr32 evmSp
  have hEvm40 : (evmSp + signExtend12 40#12 : Word) = evmSp + 40#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr40 evmSp
  have hEvm48 : (evmSp + signExtend12 48#12 : Word) = evmSp + 48#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr48 evmSp
  have hEvm56 : (evmSp + signExtend12 56#12 : Word) = evmSp + 56#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr56 evmSp
  rw [hSp0, hSp8, hSp16, hSp24, hEvm32, hEvm40, hEvm48, hEvm56]
  xperm_hyp hp

/-- Bundled precondition shared by the folded-word conditional-multiply
    adapters in both `SavedBitTwoMulCondCall` and `SavedBitTwoMulCondCanonical`.
    Hides `baseFrame` (the exponent-limb frame) and the full `foldedPre`
    assertion so spec statements can reduce to a single `let rw` binding. -/
@[irreducible]
def expCondMulFoldedPre
    (sp evmSp iterCount vOld a0 a1 a2 a3 : Word) (r : EvmWord) : Assertion :=
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
    evmWordIs sp r ** evmWordIs (evmSp + 32) r **
    baseFrame ** (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
    (.x0 ↦ᵣ (0 : Word))) **
   regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
   memOwn evmSp ** memOwn (evmSp + 8) **
   memOwn (evmSp + 16) ** memOwn (evmSp + 24))

theorem expCondMulFoldedPre_unfold
    {sp evmSp iterCount vOld a0 a1 a2 a3 : Word} {r : EvmWord} :
    expCondMulFoldedPre sp evmSp iterCount vOld a0 a1 a2 a3 r =
      (let baseFrame : Assertion :=
         ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
         ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
         ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
         ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
       (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
         evmWordIs sp r ** evmWordIs (evmSp + 32) r **
         baseFrame ** (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
         (.x0 ↦ᵣ (0 : Word))) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        memOwn evmSp ** memOwn (evmSp + 8) **
        memOwn (evmSp + 16) ** memOwn (evmSp + 24))) := by
  delta expCondMulFoldedPre; rfl

/-- Folded-word variant of the two-MUL conditional-multiply path adapter.
    The precondition consumes the current result from `sp` and the second
    multiplicand from `evmSp + 32` as `evmWordIs`, then delegates to the
    concrete-limb owned-scratch adapter via
    `exp_cond_mul_folded_pre_to_call_scratch_owned_pre`. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_folded_owned_spec_within
    (iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget : Word) (r : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulCondRw r a0 a1 a2 a3
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (expCondMulFoldedPre sp evmSp iterCount vOld a0 a1 a2 a3 r)
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] := by
  intro rw
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let foldedPre : Assertion :=
    (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
      evmWordIs sp r ** evmWordIs (evmSp + 32) r **
      baseFrame ** (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
      (.x0 ↦ᵣ (0 : Word))) **
     regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
     memOwn evmSp ** memOwn (evmSp + 8) **
     memOwn (evmSp + 16) ** memOwn (evmSp + 24))
  let concretePre : Assertion :=
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r.getLimbN 0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r.getLimbN 1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r.getLimbN 2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r.getLimbN 3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r.getLimbN 0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r.getLimbN 1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r.getLimbN 2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) **
      (.x0 ↦ᵣ (0 : Word))
    preCore **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24)
  have hConcrete :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        concretePre
        [(loopTarget,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
              expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
          (base + 264,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount = 0⌝) **
              expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] := by
    dsimp [concretePre, baseFrame]
    simpa [expTwoMulCondRwFromLimbs, expTwoMulIterW,
      expResultWord_getLimbN_self r] using
    exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_call_scratch_owned_spec_within
      iterCount sp evmSp (r.getLimbN 3) vOld
      (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3)
      a0 a1 a2 a3
      (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3)
      mulTarget squaringMulOff condMulOff skipOff backOff
      base loopTarget hbase hmt hd hback
  refine cpsNBranchWithin_weaken_pre ?_ hConcrete
  intro h hp
  simp only [expCondMulFoldedPre_unfold] at hp
  simpa [concretePre, baseFrame] using
    exp_cond_mul_folded_pre_to_call_scratch_owned_pre
      sp evmSp iterCount vOld a0 a1 a2 a3 r h hp

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

@[irreducible]
def expTwoMulCondBaseFrame (evmSp a0 a1 a2 a3 : Word) : Assertion :=
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)

theorem expTwoMulCondBaseFrame_unfold {evmSp a0 a1 a2 a3 : Word} :
    expTwoMulCondBaseFrame evmSp a0 a1 a2 a3 =
      (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  delta expTwoMulCondBaseFrame; rfl

@[irreducible]
def expTwoMulCondFrameBit (e : Word) : Assertion :=
  (.x18 ↦ᵣ (expTwoMulIterBit e + signExtend12 (0 : BitVec 12))) **
  ⌜expTwoMulIterBit e + signExtend12 (0 : BitVec 12) ≠ 0⌝

theorem expTwoMulCondFrameBit_unfold {e : Word} :
    expTwoMulCondFrameBit e =
      ((.x18 ↦ᵣ (expTwoMulIterBit e + signExtend12 (0 : BitVec 12))) **
       ⌜expTwoMulIterBit e + signExtend12 (0 : BitVec 12) ≠ 0⌝) := by
  delta expTwoMulCondFrameBit; rfl

@[irreducible]
def expTwoMulCondIterLoop
    (iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word) : Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
    expCondMulLoopRest sp evmSp base a0 a1 a2 a3
      (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) **
  expTwoMulCondFrameBit e

theorem expTwoMulCondIterLoop_unfold
    {iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word} :
    expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 =
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
        expCondMulLoopRest sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) **
      expTwoMulCondFrameBit e) := by
  delta expTwoMulCondIterLoop; rfl

@[irreducible]
def expTwoMulCondIterExit
    (iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word) : Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜expTwoMulIterCountNew iterCount = 0⌝) **
    expCondMulLoopRest sp evmSp base a0 a1 a2 a3
      (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) **
  expTwoMulCondFrameBit e

theorem expTwoMulCondIterExit_unfold
    {iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word} :
    expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 =
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) **
        expCondMulLoopRest sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) **
      expTwoMulCondFrameBit e) := by
  delta expTwoMulCondIterExit; rfl

@[irreducible]
def expTwoMulSkipIterLoop
    (iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word) : Assertion :=
  ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
    expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
    expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)

theorem expTwoMulSkipIterLoop_unfold
    {iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word} :
    expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 =
      (((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
        expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)) := by
  delta expTwoMulSkipIterLoop; rfl

@[irreducible]
def expTwoMulSkipIterExit
    (iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word) : Assertion :=
  ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜expTwoMulIterCountNew iterCount = 0⌝) **
    expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
    expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)

theorem expTwoMulSkipIterExit_unfold
    {iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 : Word} :
    expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 =
      (((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) **
        expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)) := by
  delta expTwoMulSkipIterExit; rfl

/-- One two-MUL-offset saved-bit EXP iteration with both conditional-multiply
    outcomes and both zero-bit skip outcomes exposed as separate exits. This
    composes the skip/loop-back path with the folded-word conditional-multiply
    path at the nonzero saved-bit head exit; a later slice can merge the equal
    loop/exit PCs under disjunctive postconditions. -/
theorem exp_msb_saved_bit_two_mul_full_iter_four_exit_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
    cpsNBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) **
          expTwoMulCondFrameBit e),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) **
          expTwoMulCondFrameBit e),
        (loopTarget,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
            expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)),
        (base + 264,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) **
            expTwoMulCondBaseFrame evmSp a0 a1 a2 a3))] := by
  intro rw
  let bit := expTwoMulIterBit e
  let squareW := expTwoMulSquareW r0 r1 r2 r3
  have hSkip :=
    exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_with_base_frame_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hd hskip hback
  have hCond :=
    exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_folded_owned_spec_within
      iterCount sp evmSp ((base + 44) + 68) a0 a1 a2 a3 mulTarget squareW
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hcondmt hd hback
  have hCondFramed := cpsNBranchWithin_frameR (F := expTwoMulCondFrameBit e) (by
    simp only [expTwoMulCondFrameBit_unfold]
    pcFree) hCond
  have hCondHead :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        ((((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)) **
          expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)
        [(loopTarget,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
              expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) **
            expTwoMulCondFrameBit e),
          (base + 264,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount = 0⌝) **
              expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) **
            expTwoMulCondFrameBit e)] := by
    exact cpsNBranchWithin_weaken_pre
      (fun _ hp => by
        simp only [expCondMulFoldedPre_unfold, expTwoMulCondFrameBit_unfold,
                   expTwoMulCondBaseFrame_unfold] at hp ⊢
        xperm_hyp hp) hCondFramed
  simp only [expTwoMulBaseFrame_unfold] at hSkip
  simp only [expTwoMulCondBaseFrame_unfold, expTwoMulCondFrameBit_unfold] at hCondHead
  have hFull :=
    cpsNBranchWithin_extend_head_nbranch hSkip hCondHead
  simpa [expTwoMulSkipIterRest_unfold, expTwoMulCondBaseFrame_unfold,
         expTwoMulCondFrameBit_unfold] using hFull

/-- Two-exit view of
    `exp_msb_saved_bit_two_mul_full_iter_four_exit_spec_within`, merging the
    conditional-multiply and zero-bit skip outcomes that land at the same
    loop/exit PCs. The postconditions are intentionally assertion-level
    disjunctions; later semantic slices can consume either side separately. -/
theorem exp_msb_saved_bit_two_mul_full_iter_merged_exit_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    cpsNBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)
      [(loopTarget,
          fun h => expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                   expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h),
        (base + 264,
          fun h => expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                   expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h)] := by
  let bit := expTwoMulIterBit e
  let squareW := expTwoMulSquareW r0 r1 r2 r3
  let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
  let baseFrame : Assertion := expTwoMulCondBaseFrame evmSp a0 a1 a2 a3
  let skipRest : Assertion :=
    expTwoMulSkipLoopRest bit sp evmSp base squareW
  let condFrame : Assertion :=
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let condLoop : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
      expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) ** condFrame
  let condExit : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount = 0⌝) **
      expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) ** condFrame
  let skipLoop : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame
  let skipExit : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame
  have hFour :=
    exp_msb_saved_bit_two_mul_full_iter_four_exit_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback
  refine cpsNBranchWithin_weaken_posts hFour ?_
  intro ex hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · subst ex
    refine ⟨(loopTarget, fun h =>
        expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
        expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      left
      simpa [expTwoMulCondIterLoop_unfold, expTwoMulCondFrameBit_unfold, condLoop, condFrame] using hp
  · subst ex
    refine ⟨(base + 264, fun h =>
        expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
        expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      left
      simpa [expTwoMulCondIterExit_unfold, expTwoMulCondFrameBit_unfold, condExit, condFrame] using hp
  · subst ex
    refine ⟨(loopTarget, fun h =>
        expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
        expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      right
      simpa [expTwoMulSkipIterLoop_unfold, expTwoMulCondBaseFrame_unfold,
             expTwoMulSkipIterRest_unfold, skipLoop, skipRest, baseFrame] using hp
  · subst ex
    refine ⟨(base + 264, fun h =>
        expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
        expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      right
      simpa [expTwoMulSkipIterExit_unfold, expTwoMulCondBaseFrame_unfold,
             expTwoMulSkipIterRest_unfold, skipExit, skipRest, baseFrame] using hp

/-- Branch-shaped view of the merged two-MUL saved-bit one-iteration theorem.
    This is just `cpsNBranchWithin_as_cpsBranchWithin` applied to the merged
    two-exit N-branch, keeping downstream composition code on the ordinary
    branch interface. -/
theorem exp_msb_saved_bit_two_mul_full_iter_branch_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)
      loopTarget
      (fun h => expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h)
      (base + 264)
      (fun h => expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h) := by
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_msb_saved_bit_two_mul_full_iter_merged_exit_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

/-- Owned-scratch variant of the two-MUL saved-bit one-iteration branch.
    This keeps the branch exits unchanged while exposing `x6`, `x7`, `x10`,
    and `x11` as owned caller scratch in the precondition, matching the
    boundary-frame shape produced by the prologue/pointer sequence. -/
theorem exp_msb_saved_bit_two_mul_full_iter_branch_owned_scratch_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    cpsNBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) **
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)
      [(loopTarget,
          fun h => expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                   expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h),
       (base + 264,
          fun h => expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                   expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h)] := by
  let bit := expTwoMulIterBit e
  let squareW := expTwoMulSquareW r0 r1 r2 r3
  let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
  let baseFrame : Assertion := expTwoMulCondBaseFrame evmSp a0 a1 a2 a3
  let skipRest : Assertion :=
    expTwoMulSkipLoopRest bit sp evmSp base squareW
  let condFrame : Assertion :=
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let condLoop : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
      expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) ** condFrame
  let condExit : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount = 0⌝) **
      expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw) ** condFrame
  let skipLoop : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame
  let skipExit : Assertion :=
    (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
     ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x6)
    (P :=
      (((.x5 ↦ᵣ e) ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame, expTwoMulCondBaseFrame_unfold] at hp ⊢
      xperm_hyp hp) ?_
  intro c
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x10)
    (P :=
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame, expTwoMulCondBaseFrame_unfold] at hp ⊢
      xperm_hyp hp) ?_
  intro v10
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x7)
    (P :=
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
        regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame, expTwoMulCondBaseFrame_unfold] at hp ⊢
      xperm_hyp hp) ?_
  intro v7
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x11)
    (P :=
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
        (.x7 ↦ᵣ v7) ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame, expTwoMulCondBaseFrame_unfold] at hp ⊢
      xperm_hyp hp) ?_
  intro v11
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [baseFrame, expTwoMulCondBaseFrame_unfold] at hp ⊢
      xperm_hyp hp)
    (cpsBranchWithin_as_cpsNBranchWithin
      (exp_msb_saved_bit_two_mul_full_iter_branch_spec_within
        e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
        squaringMulOff condMulOff skipOff backOff base loopTarget
        hbase hsqmt hcondmt hd hskip hback))

/-- Branch-interface view of
    `exp_msb_saved_bit_two_mul_full_iter_branch_owned_scratch_spec_within`.
    This keeps downstream full-loop composition on the ordinary two-exit
    `cpsBranchWithin` API after the scratch-register ownership lift. -/
theorem exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) **
        expTwoMulCondBaseFrame evmSp a0 a1 a2 a3)
      loopTarget
      (fun h => expTwoMulCondIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                expTwoMulSkipIterLoop iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h)
      (base + 264)
      (fun h => expTwoMulCondIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h ∨
                expTwoMulSkipIterExit iterCount e sp evmSp base r0 r1 r2 r3 a0 a1 a2 a3 h) := by
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_msb_saved_bit_two_mul_full_iter_branch_owned_scratch_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

end EvmAsm.Evm64.Exp.Compose
