/-
  EvmAsm.Evm64.MulMod.ReduceBitLoop

  Loop-facing adapter for the MULMOD 512-bit reducer. The inner-step branch
  spec clobbers and surrenders six scratch registers (`x5/x6/x7/x10/x11/x13`),
  so the bit-loop invariant carries them as ownership. This file restates the
  inner step over that loop-carried precondition.
-/

import EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The non-scratch resources carried unchanged across one reducer bit step:
    the frame pointer, the shifting product word, the bit counter, the carry
    scratch `x19/x20`, and the remainder/modulus memory windows. -/
private def bitLoopCommon
    (sp x17Old x15 x19Old x20Old : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x19 ↦ᵣ x19Old) ** (.x20 ↦ᵣ x20Old) **
  ((sp + signExtend12 (224 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (232 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (240 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (248 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Loop-carried precondition for one reducer bit step: `bitLoopCommon` plus
    ownership of the six clobbered scratch registers. -/
@[irreducible]
def mulModReduceBitLoopPre
    (sp x17Old x15 x19Old x20Old : Word) (r n : EvmWord) : Assertion :=
  bitLoopCommon sp x17Old x15 x19Old x20Old r n **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x13

/-- One reducer bit step restated over the loop-carried precondition that owns
    the six clobbered scratch registers, ready for the bit-loop induction. -/
theorem evm_mulmod_reduce512_bit_loop_step_spec_within
    (sp base x17Old x15 x19Old x20Old : Word) (r n : EvmWord) :
    cpsBranchWithin 64 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceBitLoopPre sp x17Old x15 x19Old x20Old r n)
      base (mulModReduceInnerStepPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
  have h13 : cpsBranchWithin 64 base
      (evm_mulmod_reduce512_inner_step_code base)
      ((bitLoopCommon sp x17Old x15 x19Old x20Old r n **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) **
        regOwn .x13)
      base (mulModReduceInnerStepPost sp x17Old x15 r n false)
      (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
    refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x13) ?_
    intro v13
    have h11 : cpsBranchWithin 64 base
        (evm_mulmod_reduce512_inner_step_code base)
        ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10) **
          regOwn .x11)
        base (mulModReduceInnerStepPost sp x17Old x15 r n false)
        (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
      refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x11) ?_
      intro v11
      have h10 : cpsBranchWithin 64 base
          (evm_mulmod_reduce512_inner_step_code base)
          ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
              (.x11 ↦ᵣ v11) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) **
            regOwn .x10)
          base (mulModReduceInnerStepPost sp x17Old x15 r n false)
          (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
        refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x10) ?_
        intro v10
        have h7 : cpsBranchWithin 64 base
            (evm_mulmod_reduce512_inner_step_code base)
            ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** regOwn .x5 ** regOwn .x6) **
              regOwn .x7)
            base (mulModReduceInnerStepPost sp x17Old x15 r n false)
            (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
          refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x7) ?_
          intro v7
          have h6 : cpsBranchWithin 64 base
              (evm_mulmod_reduce512_inner_step_code base)
              ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                  (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** (.x7 ↦ᵣ v7) ** regOwn .x5) **
                regOwn .x6)
              base (mulModReduceInnerStepPost sp x17Old x15 r n false)
              (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
            refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6) ?_
            intro v6
            have h5 : cpsBranchWithin 64 base
                (evm_mulmod_reduce512_inner_step_code base)
                ((bitLoopCommon sp x17Old x15 x19Old x20Old r n ** (.x13 ↦ᵣ v13) **
                    (.x11 ↦ᵣ v11) ** (.x10 ↦ᵣ v10) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6)) **
                  regOwn .x5)
                base (mulModReduceInnerStepPost sp x17Old x15 r n false)
                (base + 256) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
              refine cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x5) ?_
              intro v5
              refine cpsBranchWithin_weaken
                (fun h hp => by
                  unfold bitLoopCommon at hp
                  unfold mulModReduceInnerStepPre mulModReduceInnerStepSubtractPre
                  xperm_hyp hp)
                (fun _ hp => hp) (fun _ hp => hp)
                (evm_mulmod_reduce512_inner_step_spec_within
                  sp base x17Old v5 v6 v7 v10 v11 v13 x15 x19Old x20Old r n)
            exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
              (fun _ hp => hp) (fun _ hp => hp) h5
          exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
            (fun _ hp => hp) (fun _ hp => hp) h6
        exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun _ hp => hp) (fun _ hp => hp) h7
      exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hp => hp) (fun _ hp => hp) h10
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hp => hp) (fun _ hp => hp) h11
  exact cpsBranchWithin_weaken
    (fun h hp => by
      unfold mulModReduceBitLoopPre at hp
      xperm_hyp hp)
    (fun _ hp => hp) (fun _ hp => hp) h13

end EvmAsm.Evm64
