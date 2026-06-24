/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs

  Full-code lifting substrate for MULMOD reducer inner-step subpath specs.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix
import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
import EvmAsm.Evm64.MulMod.ReduceInnerStepTail
import EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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

end EvmAsm.Evm64
