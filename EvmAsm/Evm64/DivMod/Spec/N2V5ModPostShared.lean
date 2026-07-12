/- Shared declaration home for the n=2 MOD post bridges. -/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5FamiliesMod
import EvmAsm.Evm64.DivMod.Spec.N2V5ModRemainder
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Spec.StackPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem fullModN2UnifiedPostNoX1V5_frame_to_modConcretePostNoX1ExactRegsFrame_scratch
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hdiv1 : (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hdiv2 : (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hdiv3 : (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64))) :
    ∀ h,
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN2Shift b1)
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64))
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
  simp (config := { zeta := true }) only [fullModN2UnifiedPostNoX1V5_unfold,
    fullModN2DenormPostV5_unfold, fullDivN2FrameNoX1V5_unfold,
    fullDivN2ScratchNoX1V5_unfold, denormModPost_unfold] at hq
  rw [word_add_zero] at hq
  -- Normalize goal: unfold all bundles in one simp pass.
  rw [modConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64))
        hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hq

/-- Named callable-frame bridge for n=2: converts `fullModN2UnifiedPostNoX1V5`
    plus exact `x1` to `modStackDispatchPostCallableExactFrame` plus the v4
    scratch cell. Mirrors `fullDivN3UnifiedPostNoX1V5_frame_to_divStack…_scratch`
    in N3V5StackPre.lean:840. -/
theorem fullModN2UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hdiv1 : (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hdiv2 : (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hdiv3 : (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64))) :
    ∀ h,
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hp
  rw [modStackDispatchPostCallableExactFrame_unfold]
  exact sepConj_mono_left
    (fun h hp => modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h
    (fullModN2UnifiedPostNoX1V5_frame_to_modConcretePostNoX1ExactRegsFrame_scratch
      bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem
      raVal ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp)

/-- Word-quotient form: from `hdivWord : fullModN2RemainderWordV5 ... = EvmWord.mod a b`
    directly. Mirrors `fullDivN3…_scratch_word` in N3V5StackPre.lean:875. -/
theorem fullModN2UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullModN2RemainderWordV5 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    ∀ h,
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) h := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullModN2V5_hmods_of_word_eq a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      bltu_2 bltu_1 bltu_0
      hdivWord
  exact fullModN2UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch
    bltu_2 bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3


open EvmAsm.Rv64

/-- From the n=2 v5 unified post (with exact caller `x1`) and quotient
    correctness, conclude the scaffold post `modStackDispatchPostV5`. -/
theorem fullModN2UnifiedPostNoX1V5_to_modStackDispatchPostV5
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullModN2RemainderWordV5 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    ∀ h,
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      modStackDispatchPostV5 sp a b h := by
  intro h hp
  have h1 := fullModN2UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
    bltu_2 bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hp
  simp only [modStackDispatchPostV5]
  revert h1
  apply sepConj_mono
  · exact fun h hp =>
      modStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h hp
  · exact fun h hp => memIs_implies_memOwn h hp

end EvmAsm.Evm64
