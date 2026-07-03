/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallableExactOfShapeMod

  MOD mirror of `N2V5CallableExactOfShape`: the v5 n=2 MOD callable exact-frame
  lane, shape-level combiner.  The shift≠0 arm composes the x9In/x2In-generic
  body spec `evm_mod_n2_stack_pre_to_unified_post_v5_noNop_fromShape` with the
  callable wrapper `evm_mod_n2_..._callableExactFrame_uni` (which applies the mod
  callable exact-frame post bridge).  The shift=0 arm + the `of_shape` combiner
  land the same mod callable exact-frame post (`x1 = raVal`, `x9 = signExtend12
  4095`).  Feeds the callable 5-lane MOD scaffold `lane_n2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5CallableExactMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFromShapeMod
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientLaneShapeMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneShift0Mod
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0PreLift

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- n=2 v5 MOD callable exact-frame lane, shift≠0 arm.  Mirrors the DIV
    `evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz`, using the
    mod remainder-word shape lemma + the mod `_fromShape` body + the mod `_uni`
    wrapper. -/
theorem evm_mod_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  obtain ⟨bltu_2, hbltu_2⟩ :
      ∃ x, x = BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 := ⟨_, rfl⟩
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 := ⟨_, rfl⟩
  have hc2 : bltu_2 = true →
      BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 = true := fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false →
      ¬ BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 := fun h => by rw [← hbltu_2, h]; decide
  have hc1 : bltu_1 = true →
      BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 = true := fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 := fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 = true := fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 := fun h => by rw [← hbltu_0, h]; decide
  have hdivWord := fullModN2RemainderWordV5_eq_mod_lane_of_shape bltu_2 bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  have hbody := evm_mod_n2_stack_pre_to_unified_post_v5_noNop_fromShape sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal x9In x2In
    bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2 hbltu_1 hbltu_0
  exact evm_mod_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_uni
    bltu_2 bltu_1 bltu_0 sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal x9In x2In
    hdivWord hbody

/-- Shift=0 CALLABLE post bridge (MOD): the flag-param full shift=0 path post →
    `modStackDispatchPostCallableExactFrame` (x1 = raVal, x9 = signExtend12 4095)
    with the scratch cell weakened to `memOwn`.  Copies the reshaping of the
    dispatched `n2_shift0_fullPost_to_modStackDispatchPostV5` but stops at the
    callable exact frame (via `modConcretePostNoX1ExactRegs_weaken_callable_frame`)
    instead of weakening on to `modStackDispatchPostV5`. -/
theorem n2_shift0_fullPost_to_modStackDispatchPostCallableExactFrame
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.mod a b).getLimbN 0 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1)
    (hdiv1 : (EvmWord.mod a b).getLimbN 1 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1)
    (hdiv2 : (EvmWord.mod a b).getLimbN 2 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1)
    (hdiv3 : (EvmWord.mod a b).getLimbN 3 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        (.x6 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        (.x7 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        (.x2 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1) **
        ((sp + signExtend12 4056) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        ((sp + signExtend12 4048) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        ((sp + signExtend12 4040) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        ((sp + signExtend12 4032) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        ((sp + 32) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1) **
        ((sp + 40) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1) **
        ((sp + 48) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1) **
        ((sp + 56) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1)) **
       fullModN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
         retMem dMem dloMem scratchUn0 scratchMem raVal) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hq
  rw [fullModN2FrameShift0V5_unfold] at hq
  have hExact :
      (modConcretePostNoX1ExactRegsFrame sp a b (signExtend12 4095) raVal
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
        (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1
        (n2Shift0R2 bltu_2 a2 a3 b0 b1).1
        (0 : Word)
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.2
        (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).2.2.2.2.2
        (n2Shift0R2 bltu_2 a2 a3 b0 b1).2.2.2.2.2
        (0 : Word)
        (clzResult b1).1 (2 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff)
          else if bltu_2 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then b1 else if bltu_1 then b1 else if bltu_2 then b1 else dMem)
        (if bltu_0 then divKTrialCallV5DLo b1
          else if bltu_1 then divKTrialCallV5DLo b1
          else if bltu_2 then divKTrialCallV5DLo b1 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0 (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).2.1
          else if bltu_1 then divKTrialCallV5Un0 (n2Shift0R2 bltu_2 a2 a3 b0 b1).2.1
          else if bltu_2 then divKTrialCallV5Un0 a3 else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ n2Shift0ModScratchMemF bltu_2 bltu_1 bltu_0 a1 a2 a3 b0 b1 scratchMem)) h := by
    rw [modConcretePostNoX1ExactRegsFrame_unfold,
        evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
        evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.1
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.1
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.1
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1 hdiv0 hdiv1 hdiv2 hdiv3,
        divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
    delta n2Shift0ModScratchMemF
    rw [word_add_zero] at hq
    xperm_hyp hq
  exact sepConj_mono
    (fun h hp => by
      rw [modStackDispatchPostCallableExactFrame_unfold]
      exact modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    (fun h hp => memIs_implies_memOwn h hp)
    h hExact

end EvmAsm.Evm64
