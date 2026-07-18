/- Shared declaration home for the n=2 DIV concrete and dispatch-post bridges. -/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientShared
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Spec.StackPostBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem fullDivN2UnifiedPostNoX1V5_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN2Shift b1)
        (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64))
        (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (0 : Word)
        (fullDivN2Shift b1) (2 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff)
          else if bltu_2 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_1 then (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_2 then (fullDivN2NormV b0 b1 b2 b3).2.1 else dMem)
        (if bltu_0 then divKTrialCallV5DLo (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_1 then divKTrialCallV5DLo (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_2 then divKTrialCallV5DLo (fullDivN2NormV b0 b1 b2 b3).2.1 else dloMem)
        (if bltu_0 then
            divKTrialCallV5Un0 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
          else if bltu_1 then
            divKTrialCallV5Un0 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
          else if bltu_2 then
            divKTrialCallV5Un0 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hq
  -- Normalize hq: expand all @[irreducible] V5 bundles and inline let-bindings.
  simp (config := { zeta := true }) only [fullDivN2UnifiedPostNoX1V5_unfold,
    fullDivN2DenormPostV5_unfold, fullDivN2FrameNoX1V5_unfold,
    fullDivN2ScratchNoX1V5_unfold, denormDivPost_unfold] at hq
  rw [word_add_zero] at hq
  -- Normalize goal: unfold all bundles in one simp pass.
  rw [divConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b)
        (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word) hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hq

/-- Derive per-limb V5 quotient conditions from the word equality. -/
theorem fullDivN2_hdivs_v5_of_word_eq
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3

/-- Named callable-frame bridge for n=2: converts `fullDivN2UnifiedPostNoX1V5`
    plus exact `x1` to `divStackDispatchPostCallableExactFrame` plus the v4
    scratch cell. Mirrors `fullDivN3UnifiedPostNoX1V5_frame_to_divStack…_scratch`
    in N3V5StackPre.lean:840. -/
theorem fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  exact sepConj_mono_left
    (fun h hp => divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h
    (fullDivN2UnifiedPostNoX1V5_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
      bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem
      raVal ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp)

/-- Word-quotient form: from `hdivWord : fullDivN2QuotientWordV5 ... = EvmWord.div a b`
    directly. Mirrors `fullDivN3…_scratch_word` in N3V5StackPre.lean:875. -/
theorem fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) h := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN2_hdivs_v5_of_word_eq bltu_2 bltu_1 bltu_0 a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch
    bltu_2 bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3


open EvmAsm.Rv64

/-- From the n=2 v5 unified post (with exact caller `x1`) and quotient
    correctness, conclude the scaffold post `divStackDispatchPostV5`. -/
theorem fullDivN2UnifiedPostNoX1V5_to_divStackDispatchPostV5
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      divStackDispatchPostV5 sp a b h := by
  intro h hp
  have h1 := fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
    bltu_2 bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hp
  simp only [divStackDispatchPostV5]
  revert h1
  apply sepConj_mono
  · exact fun h hp =>
      divStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h hp
  · exact fun h hp => memIs_implies_memOwn h hp

end EvmAsm.Evm64
