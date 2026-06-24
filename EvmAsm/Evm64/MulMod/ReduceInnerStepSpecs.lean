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
import EvmAsm.Rv64.Tactics.XPermPure

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



/-- Subtract-store precondition with compare-clobbered registers kept as ownership. -/
@[irreducible]
def mulModReduceSubtractOwnPre
    (sp v5 v10 v11 v13 : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
  mulModReduceCompareMem sp r n

theorem evm_mulmod_reduce512_inner_step_subtract_store_own_full_code_spec_within
    (sp base v5 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 26 (base + 144) (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceSubtractOwnPre sp v5 v10 v11 v13 r n)
      (mulModReduceSubtractPost sp r n) := by
  have hown7 : cpsTripleWithin 26 (base + 144) (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** regOwn .x6 **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
        mulModReduceCompareMem sp r n) ** regOwn .x7)
      (mulModReduceSubtractPost sp r n) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7) ?_
    intro v7
    have hown6 : cpsTripleWithin 26 (base + 144) (base + 248)
        (evm_mulmod_reduce512_inner_step_code base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
          mulModReduceCompareMem sp r n ** (.x7 ↦ᵣ v7)) ** regOwn .x6)
        (mulModReduceSubtractPost sp r n) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6) ?_
      intro v6
      exact cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp)
        (fun _ hp => hp)
        (evm_mulmod_reduce512_inner_step_subtract_store_full_code_spec_within
          sp base v5 v6 v7 v10 v11 v13 r n)
    exact cpsTripleWithin_weaken (fun h hp => by
        xperm_hyp hp)
      (fun _ hp => hp) hown6
  exact cpsTripleWithin_weaken (fun h hp => by
      unfold mulModReduceSubtractOwnPre at hp
      xperm_hyp hp)
    (fun _ hp => hp) hown7

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


/-- Folded precondition for the reducer inner-step subtract path. -/
@[irreducible]
def mulModReduceInnerStepSubtractPre
    (sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) **
  (.x7 ↦ᵣ x7Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
  (.x13 ↦ᵣ x13Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x19 ↦ᵣ x19Old) ** (.x20 ↦ᵣ x20Old) **
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded postcondition for the reducer inner-step subtract path. -/
@[irreducible]
def mulModReduceInnerStepSubtractPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool) : Assertion :=
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  mulModReduceTailPost x15 done **
  mulModReduceSubtractPost sp shifted n **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
  (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
  ⌜mulModReduceRemGE shifted n⌝

/-- Compose prefix, compare-GE, subtract-store, and tail into the subtract reducer path. -/
theorem evm_mulmod_reduce512_inner_step_subtract_path_spec_within
    (sp base x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord)
    (hge : mulModReduceRemGE (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    cpsBranchWithin 64 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemGE (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n⌝)
      base (mulModReduceInnerStepSubtractPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepSubtractPost sp x17Old x15 r n true) := by
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  let prefixFrame : Assertion :=
    (.x7 ↦ᵣ x7Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
    (.x13 ↦ᵣ x13Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
    ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
    ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
    ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
    ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
    ⌜mulModReduceRemGE shifted n⌝
  let compareFrame : Assertion :=
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) **
    (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))
  let subtractFrame : Assertion :=
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜mulModReduceRemGE shifted n⌝
  let tailFrame : Assertion :=
    mulModReduceSubtractPost sp shifted n **
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    ⌜mulModReduceRemGE shifted n⌝
  have hprefix0 := evm_mulmod_reduce512_inner_step_shift_prefix_full_code_spec_within
    sp base x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
    (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) x5Old x6Old x19Old x20Old
  have hprefix := cpsTripleWithin_frameR prefixFrame (by pcFree) hprefix0
  have hprefixTop : cpsTripleWithin 21 base (base + 84)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemGE shifted n⌝)
      (mulModReduceShiftPrefixPost sp x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
        (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) ** prefixFrame) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold mulModReduceInnerStepSubtractPre at hp
      dsimp only [prefixFrame, shifted] at hp ⊢
      xperm_hyp hp)
      (fun _ hp => hp) hprefix
  have hcompare0 := evm_mulmod_reduce512_inner_step_compare_ge_full_code_spec_within
    sp base (EvmWord.getLimbN shifted 3) x7Old shifted n hge
  have hcompare := cpsTripleWithin_frameR compareFrame (by pcFree) hcompare0
  have hprefix_compare : cpsTripleWithin (21 + 15) base (base + 144)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemGE shifted n⌝)
      (mulModReduceComparePost sp shifted n true ** compareFrame) :=
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
  have hsubtract0 := evm_mulmod_reduce512_inner_step_subtract_store_own_full_code_spec_within
    sp base (EvmWord.getLimbN r 3) x10Old x11Old x13Old shifted n
  have hsubtract := cpsTripleWithin_frameR subtractFrame (by pcFree) hsubtract0
  have hthrough_subtract : cpsTripleWithin (21 + 15 + 26) base (base + 248)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemGE shifted n⌝)
      (mulModReduceSubtractPost sp shifted n ** subtractFrame) :=
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold mulModReduceComparePost at hp
      unfold mulModReduceSubtractOwnPre
      unfold mulModReduceCompareMem at hp ⊢
      simp only [ite_true] at hp
      dsimp only [compareFrame, subtractFrame] at hp ⊢
      xperm_hyp hp)
      hprefix_compare hsubtract
  have htail0 := evm_mulmod_reduce512_inner_step_tail_full_code_spec_within base x15
  have htail := cpsBranchWithin_frameR tailFrame (by
    dsimp only [tailFrame]
    unfold mulModReduceSubtractPost mulModReduceSubtractMem
    pcFree) htail0
  have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun h hp => by
      dsimp only [subtractFrame, tailFrame] at hp ⊢
      xperm_hyp hp)
    hthrough_subtract htail
  change cpsBranchWithin (21 + 15 + 26 + 2) base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemGE shifted n⌝)
      base (mulModReduceInnerStepSubtractPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepSubtractPost sp x17Old x15 r n true)
  exact cpsBranchWithin_weaken (fun _ hp => hp) (fun h hp => by
      unfold mulModReduceInnerStepSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      unfold mulModReduceInnerStepSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    hbranch


/-! ## Full reducer inner-step composition

Compose the subtract and no-subtract reducer inner-step paths into one
branch specification whose folded post records a single bit step
`mulModReduceStep`: it shifts the consumed product bit into the remainder
and conditionally subtracts the modulus. -/

/-- Under the no-subtract (`<`) branch the bit step keeps the shifted-in
    remainder unchanged. -/
theorem mulModReduceStep_of_lt {r n : EvmWord} {bit : Bool}
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r bit) n) :
    mulModReduceStep r n bit = mulModReduceShiftInBit r bit := by
  have hlt' : (mulModReduceShiftInBit r bit).toNat < n.toNat := by
    unfold mulModReduceRemLT at hlt
    simpa only [BitVec.ult, decide_eq_true_eq] using hlt
  unfold mulModReduceStep
  simp only [hlt', if_true]

/-- Under the subtract (`≥`) branch the bit step subtracts the modulus from
    the shifted-in remainder. -/
theorem mulModReduceStep_of_ge {r n : EvmWord} {bit : Bool}
    (hge : mulModReduceRemGE (mulModReduceShiftInBit r bit) n) :
    mulModReduceStep r n bit = mulModReduceShiftInBit r bit - n := by
  have hge' : ¬ (mulModReduceShiftInBit r bit).toNat < n.toNat := by
    unfold mulModReduceRemGE at hge
    simpa only [BitVec.ult, decide_eq_true_eq] using hge
  unfold mulModReduceStep
  simp only [hge', if_false]

/-- Folded precondition for the full reducer inner step.

It owns the loop-carried registers and the remainder/modulus memory window,
agreeing with the subtract-path precondition so both branch paths share it. -/
@[irreducible]
def mulModReduceInnerStepPre
    (sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord) : Assertion :=
  mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old
    x15 x19Old x20Old r n

/-- Folded postcondition for the full reducer inner step.

The remainder window at `sp + 224..248` holds the limbs of one semantic step
`mulModReduceStep r n bit` (shift the consumed bit in, conditionally subtract
the modulus); the modulus window at `sp + 64..88` is preserved; the loop
counter `x15` is decremented and the `done` flag records whether it reached
zero. The scratch registers clobbered along the way are surrendered as
ownership. -/
@[irreducible]
def mulModReduceInnerStepPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool) : Assertion :=
  let stepped := mulModReduceStep r n (mulModReduceInputBit x17Old)
  mulModReduceTailPost x15 done **
  (.x12 ↦ᵣ sp) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
  (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
  mulModReduceCompareMem sp stepped n

/-- Surrender the subtract-path scratch registers as ownership. -/
theorem mulModReduceSubtractPost_regOwn (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceSubtractPost sp r n h →
      ((.x12 ↦ᵣ sp) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
       mulModReduceSubtractMem sp r n) h := by
  intro h hp
  unfold mulModReduceSubtractPost at hp
  have hp1 := sepConj_mono_right (sepConj_mono_left
    (regIs_to_regOwn .x5 _)) h hp
  have hp2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (regIs_to_regOwn .x6 _))) h hp1
  have hp3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp2
  have hp4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _))))) h hp3
  have hp5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (regIs_to_regOwn .x11 _)))))) h hp4
  have hp6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (regIs_to_regOwn .x13 _))))))) h hp5
  xperm_hyp hp6

/-- Bridge the subtract-path post into the unified inner-step post. -/
theorem mulModReduceInnerStepPost_of_subtractPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool)
    (hge : mulModReduceRemGE (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    ∀ h, mulModReduceInnerStepSubtractPost sp x17Old x15 r n done h →
      mulModReduceInnerStepPost sp x17Old x15 r n done h := by
  intro h hp
  unfold mulModReduceInnerStepSubtractPost at hp
  have hp1 := sepConj_mono_right (sepConj_mono_left
    (mulModReduceSubtractPost_regOwn sp
      (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n)) h hp
  unfold mulModReduceInnerStepPost mulModReduceCompareMem
  unfold mulModReduceSubtractMem at hp1
  rw [mulModReduceStep_of_ge hge]
  xperm_pure hp1

/-- Drop the path-selecting pure fact carried by the compare-ladder post. -/
theorem mulModReduceComparePost_drop (sp : Word) (r n : EvmWord) (b : Bool) :
    ∀ h, mulModReduceComparePost sp r n b h →
      ((.x12 ↦ᵣ sp) ** regOwn .x6 ** regOwn .x7 ** mulModReduceCompareMem sp r n) h := by
  intro h hp
  unfold mulModReduceComparePost at hp
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (fun _ hq => ((sepConj_pure_right _).1 hq).1))) h hp

/-- Bridge the no-subtract-path post (with the frame-in scratch registers)
    into the unified inner-step post. -/
theorem mulModReduceInnerStepPost_of_noSubtractPost
    (sp x17Old x10Old x11Old x13Old x15 : Word) (r n : EvmWord) (done : Bool)
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    ∀ h, (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n done **
            ((.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old))) h →
      mulModReduceInnerStepPost sp x17Old x15 r n done h := by
  intro h hp
  unfold mulModReduceInnerStepNoSubtractPost at hp
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
    (mulModReduceComparePost_drop sp
      (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n false))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 _))))) h hp1
  have hp3 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h hp2
  have hp4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (regIs_to_regOwn .x11 _))) h hp3
  have hp5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (regIs_to_regOwn .x13 _))) h hp4
  unfold mulModReduceInnerStepPost
  rw [mulModReduceStep_of_lt hlt]
  xperm_hyp hp5

/-- Full reducer inner-step branch specification: one bit-serial step of the
    512-bit modular reduction, dispatching the subtract / no-subtract paths on
    the comparison of the shifted remainder against the modulus. -/
theorem evm_mulmod_reduce512_inner_step_spec_within
    (sp base x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord) :
    cpsBranchWithin 64 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepPre sp x17Old x5Old x6Old x7Old x10Old x11Old x13Old
        x15 x19Old x20Old r n)
      base (mulModReduceInnerStepPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
  by_cases hge : mulModReduceRemGE (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n
  · have hsub := evm_mulmod_reduce512_inner_step_subtract_path_spec_within
      sp base x17Old x5Old x6Old x7Old x10Old x11Old x13Old x15 x19Old x20Old r n hge
    exact cpsBranchWithin_weaken
      (fun h hp => by
        unfold mulModReduceInnerStepPre at hp
        exact (sepConj_pure_right h).2 ⟨hp, hge⟩)
      (mulModReduceInnerStepPost_of_subtractPost sp x17Old x15 r n false hge)
      (mulModReduceInnerStepPost_of_subtractPost sp x17Old x15 r n true hge)
      hsub
  · have hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n := by
      unfold mulModReduceRemGE at hge
      unfold mulModReduceRemLT
      exact not_not.mp hge
    have hns0 := evm_mulmod_reduce512_inner_step_no_subtract_path_spec_within
      sp base x17Old x5Old x6Old x7Old x15 x19Old x20Old r n hlt
    have hns1 := cpsBranchWithin_frameR
      ((.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old)) (by pcFree) hns0
    have hns := cpsBranchWithin_mono_nSteps (show (38 : Nat) ≤ 64 by omega) hns1
    exact cpsBranchWithin_weaken
      (fun h hp => by
        unfold mulModReduceInnerStepPre mulModReduceInnerStepSubtractPre at hp
        unfold mulModReduceInnerStepNoSubtractPre
        have hp2 := (sepConj_pure_right h).2 ⟨hp, hlt⟩
        xperm_hyp hp2)
      (mulModReduceInnerStepPost_of_noSubtractPost sp x17Old x10Old x11Old x13Old x15 r n false hlt)
      (mulModReduceInnerStepPost_of_noSubtractPost sp x17Old x10Old x11Old x13Old x15 r n true hlt)
      hns

end EvmAsm.Evm64
