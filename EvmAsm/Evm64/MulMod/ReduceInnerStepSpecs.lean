/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs

  Full-code lifting substrate for MULMOD reducer inner-step subpath specs.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix
import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
import EvmAsm.Evm64.MulMod.ReduceInnerStepTail
import EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- Full code requirement for one reducer inner step. -/
abbrev evm_mulmod_reduce512_inner_step_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_reduce512_inner_step

theorem evm_mulmod_reduce512_inner_step_shift_prefix_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_shift_prefix_code base a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_shift_prefix_code
  unfold evm_mulmod_reduce512_inner_step_code
  refine CodeReq.ofProg_mono_sub base base
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_shift_prefix
    0 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]
    bv_omega
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_compare_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_code base a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_compare_code
  unfold evm_mulmod_reduce512_inner_step_code
  refine CodeReq.ofProg_mono_sub base (base + 84)
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_compare
    21 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 21) = (84 : Word) by decide]
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_subtract_store_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_subtract_store_code base a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_subtract_store_code
  unfold evm_mulmod_reduce512_inner_step_code
  refine CodeReq.ofProg_mono_sub base (base + 144)
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_subtract_store
    36 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 36) = (144 : Word) by decide]
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_tail_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_tail_code base a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_tail_code
  unfold evm_mulmod_reduce512_inner_step_code
  refine CodeReq.ofProg_mono_sub base (base + 248)
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_tail
    62 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 62) = (248 : Word) by decide]
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_shift_prefix_full_code_spec_within
    (sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20 : Word) :
    cpsTripleWithin 21 base (base + 84)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ r3))
      (mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_shift_prefix_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_shift_prefix_spec_within
      sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20)

theorem evm_mulmod_reduce512_inner_step_compare_ge_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hge : mulModReduceRemGE r n) :
    cpsTripleWithin 15 (base + 84) (base + 144)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceComparePre sp x6Old x7Old r n ** ⌜mulModReduceRemGE r n⌝)
      (mulModReduceComparePost sp r n true) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_ge_spec_within
      sp base x6Old x7Old r n hge)

theorem evm_mulmod_reduce512_inner_step_compare_lt_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hlt : mulModReduceRemLT r n) :
    cpsTripleWithin 15 (base + 84) (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceComparePre sp x6Old x7Old r n ** ⌜mulModReduceRemLT r n⌝)
      (mulModReduceComparePost sp r n false) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_lt_spec_within
      sp base x6Old x7Old r n hlt)

theorem evm_mulmod_reduce512_inner_step_subtract_store_full_code_spec_within
    (sp base v5 v6 v7 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 26 (base + 144) (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
       mulModReduceCompareMem sp r n)
      (mulModReduceSubtractPost sp r n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_subtract_store_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_subtract_store_spec_within
      sp base v5 v6 v7 v10 v11 v13 r n)

theorem evm_mulmod_reduce512_inner_step_tail_full_code_spec_within
    (base x15 : Word) :
    cpsBranchWithin 2 (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)))
      base (mulModReduceTailPost x15 false)
      (base + 256) (mulModReduceTailPost x15 true) :=
  cpsBranchWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_tail_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_tail_spec_within base x15)

theorem evm_mulmod_reduce512_inner_step_tail_done_full_code_spec_within
    (base x15 : Word)
    (h_done : x15 + signExtend12 (4095 : BitVec 12) = 0) :
    cpsTripleWithin 2 (base + 248) (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) = 0⌝)
      (mulModReduceTailPost x15 true) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_tail_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_tail_done_spec_within base x15 h_done)

theorem evm_mulmod_reduce512_inner_step_tail_loop_full_code_spec_within
    (base x15 : Word)
    (h_loop : x15 + signExtend12 (4095 : BitVec 12) ≠ 0) :
    cpsTripleWithin 2 (base + 248) base
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) ≠ 0⌝)
      (mulModReduceTailPost x15 false) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_tail_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_tail_loop_spec_within base x15 h_loop)


/-- Folded precondition for the reducer inner-step no-subtract path. -/
@[irreducible]
def mulModReduceInnerStepNoSubtractPre
    (sp x17Old x5Old x6Old x7Old x15 x19Old x20Old : Word)
    (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) **
  (.x7 ↦ᵣ x7Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x19 ↦ᵣ x19Old) ** (.x20 ↦ᵣ x20Old) **
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded postcondition for the reducer inner-step no-subtract path. -/
@[irreducible]
def mulModReduceInnerStepNoSubtractPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool) : Assertion :=
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  mulModReduceTailPost x15 done **
  mulModReduceComparePost sp shifted n false **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
  (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
  (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63))

/-- Compose prefix, compare-LT, and tail into the no-subtract reducer inner-step path. -/
theorem evm_mulmod_reduce512_inner_step_no_subtract_path_spec_within
    (sp base x17Old x5Old x6Old x7Old x15 x19Old x20Old : Word)
    (r n : EvmWord)
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    cpsBranchWithin 38 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n⌝)
      base (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n true) := by
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  let prefixFrame : Assertion :=
    (.x7 ↦ᵣ x7Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
    ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
    ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
    ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
    ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
    ⌜mulModReduceRemLT shifted n⌝
  let compareFrame : Assertion :=
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))
  let tailFrame : Assertion :=
    mulModReduceComparePost sp shifted n false **
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63))
  have hprefix0 := evm_mulmod_reduce512_inner_step_shift_prefix_full_code_spec_within
    sp base x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
    (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) x5Old x6Old x19Old x20Old
  have hprefix := cpsTripleWithin_frameR prefixFrame (by pcFree) hprefix0
  have hprefixTop : cpsTripleWithin 21 base (base + 84)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      (mulModReduceShiftPrefixPost sp x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
        (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) ** prefixFrame) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold mulModReduceInnerStepNoSubtractPre at hp
      dsimp only [prefixFrame, shifted] at hp ⊢
      xperm_hyp hp)
      (fun _ hp => hp) hprefix
  have hcompare0 := evm_mulmod_reduce512_inner_step_compare_lt_full_code_spec_within
    sp base (EvmWord.getLimbN shifted 3) x7Old shifted n hlt
  have hcompare := cpsTripleWithin_frameR compareFrame (by pcFree) hcompare0
  have hprefix_compare : cpsTripleWithin (21 + 15) base (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      (mulModReduceComparePost sp shifted n false ** compareFrame) :=
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold mulModReduceShiftPrefixPost at hp
      have hrem : mulModReduceRemWord (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
          (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) = r := by
        apply (EvmWord.eq_iff_limbs).2
        intro i
        fin_cases i <;> simp [EvmWord.getLimb_as_getLimbN_0,
          EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
          EvmWord.getLimb_as_getLimbN_3]
      rw [hrem] at hp
      unfold mulModReduceComparePre mulModReduceCompareMem
      dsimp only [shifted, prefixFrame, compareFrame] at hp ⊢
      xperm_hyp hp)
      hprefixTop hcompare
  have htail0 := evm_mulmod_reduce512_inner_step_tail_full_code_spec_within base x15
  have htail := cpsBranchWithin_frameR tailFrame (by
    dsimp only [tailFrame]
    unfold mulModReduceComparePost mulModReduceCompareMem
    pcFree) htail0
  have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun h hp => by
      dsimp only [compareFrame, tailFrame] at hp ⊢
      xperm_hyp hp)
    hprefix_compare htail
  change cpsBranchWithin (21 + 15 + 2) base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      base (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n true)
  exact cpsBranchWithin_weaken (fun _ hp => hp) (fun h hp => by
      unfold mulModReduceInnerStepNoSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      unfold mulModReduceInnerStepNoSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    hbranch

end EvmAsm.Evm64
