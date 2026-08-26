module

public import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostDefs

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_named_posts_spec_within
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
       expTwoMulIterBaseFrame evmSp a0 a1 a2 a3)
      loopTarget
        (fun h =>
          expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e) sp evmSp
            base a0 a1 a2 a3 (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
            (expTwoMulIterCountNew iterCount ≠ 0) h ∨
          expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e) sp evmSp
            base a0 a1 a2 a3 (expTwoMulSquareW r0 r1 r2 r3)
            (expTwoMulIterCountNew iterCount ≠ 0) h)
      (base + 264)
        (fun h =>
          expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e) sp evmSp
            base a0 a1 a2 a3 (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
            (expTwoMulIterCountNew iterCount = 0) h ∨
          expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e) sp evmSp
            base a0 a1 a2 a3 (expTwoMulSquareW r0 r1 r2 r3)
            (expTwoMulIterCountNew iterCount = 0) h) := by
  rw [expTwoMulIterBaseFrame_unfold, ← expTwoMulCondBaseFrame_unfold]
  exact cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      simp only [expTwoMulCondIterLoop_unfold, expTwoMulSkipIterLoop_unfold] at hp
      rcases hp with hp | hp
      · left
        simpa [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
          expTwoMulIterCondFrame_unfold, expCondMulLoopRest_unfold,
          expTwoMulCondFrameBit_unfold] using hp
      · right
        simpa [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
          expTwoMulSkipLoopRest_unfold, expTwoMulIterBaseFrame_unfold,
          expTwoMulCondBaseFrame_unfold, expTwoMulSkipIterRest_unfold] using hp)
    (fun _ hp => by
      simp only [expTwoMulCondIterExit_unfold, expTwoMulSkipIterExit_unfold] at hp
      rcases hp with hp | hp
      · left
        simpa [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
          expTwoMulIterCondFrame_unfold, expCondMulLoopRest_unfold,
          expTwoMulCondFrameBit_unfold] using hp
      · right
        simpa [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
          expTwoMulSkipLoopRest_unfold, expTwoMulIterBaseFrame_unfold,
          expTwoMulCondBaseFrame_unfold, expTwoMulSkipIterRest_unfold] using hp)
    (exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

theorem exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_named_loop_exit_spec_within
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
       expTwoMulIterBaseFrame evmSp a0 a1 a2 a3)
      loopTarget
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  exact cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [expTwoMulIterLoopPost_unfold]
      exact hp)
    (fun _ hp => by
      rw [expTwoMulIterExitPost_unfold]
      exact hp)
    (by
      simpa [expTwoMulIterBit, expTwoMulIterW, expTwoMulIterAw,
        expTwoMulIterRw, expTwoMulIterCountNew] using
        (exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_named_posts_spec_within
          e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
          squaringMulOff condMulOff skipOff backOff base loopTarget
          hbase hsqmt hcondmt hd hskip hback))

theorem exp_msb_saved_bit_two_mul_full_iter_named_pre_loop_exit_spec_within
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
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3)
      loopTarget
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  exact cpsBranchWithin_weaken
    (fun _ hp => by
      rw [expTwoMulIterPre_unfold] at hp
      exact hp)
    (fun _ hp => hp)
    (fun _ hp => hp)
    (exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_named_loop_exit_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

theorem exp_msb_saved_bit_two_mul_full_iter_named_pre_loopback_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = base + 28) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3)
      (base + 28)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  exact
    exp_msb_saved_bit_two_mul_full_iter_named_pre_loop_exit_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff skipOff backOff base (base + 28)
      hbase hsqmt hcondmt hd hskip hback

theorem exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_branches_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff
              EvmAsm.Evm64.canonicalExpCondMulSkipOff
              EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff)
            (mul_callable_code mulTarget)) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3)
      (base + 28)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  have hskip :
      (base + 148 : Word) +
        signExtend13 EvmAsm.Evm64.canonicalExpCondMulSkipOff = base + 256 := by
    exact EvmAsm.Evm64.canonicalExpCondMulSkip_target base
  have hback :
      ((base + 256) + 4 : Word) +
        signExtend13 EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff = base + 28 := by
    exact EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBack_target base
  exact
    exp_msb_saved_bit_two_mul_full_iter_named_pre_loopback_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base hbase hsqmt hcondmt hd hskip hback

/-- Canonical-code view of the named-pre two-MUL iteration spec. This packages
    the canonical branch offsets behind `evmExpMsbSavedBitTwoMulCanonicalCode`,
    leaving only the two external MUL-call offsets visible to callers. -/
theorem exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_code_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3)
      (base + 28)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  exact
    exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_branches_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff base hbase hsqmt hcondmt hd

/-- Canonical combined-code view of the named-pre two-MUL iteration spec.
    This is the loop-body shape used by the canonical full-loop boundary
    wrappers. -/
theorem exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_with_mul_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3)
      (base + 28)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  exact
    exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_code_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff base hbase hsqmt hcondmt hd

/-- Canonical combined-code view of the named-pre two-MUL iteration spec with
    `mul_callable` appended immediately after the 304-byte EXP wrapper. -/
theorem exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_appended_mul_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3)
      (base + 28)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (base + 264)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)) := by
  exact
    exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_with_mul_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 (base + 304)
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      base hbase
      (EvmAsm.Evm64.canonicalExpSquaringMul_target base).symm
      (EvmAsm.Evm64.canonicalExpCondMul_target base).symm
      (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

end EvmAsm.Evm64.Exp.Compose
