/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallableExactOfShape

  The v5 n=2 DIV callable exact-frame lane, shape-level combiner: mirrors the
  n=1/n=3/n=4 `..._callableExactFrame_of_shape` lanes.  The shift≠0 arm composes
  the x9In-generic body spec `evm_div_n2_stack_pre_to_unified_post_v5_noNop_fromShape`
  with the callable wrapper `..._callableExactFrame_uni` (which applies the
  callable exact-frame post bridge).  The shift=0 arm and the `of_shape` combiner
  land the same callable exact-frame post (`x1 = raVal`, `x9 = signExtend12 4095`).
  Feeds the callable 5-lane scaffold `lane_n2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5CallableExact
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFromShape
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientShared
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0QuotientLane
import EvmAsm.Evm64.DivMod.DivN2V5ShiftShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- n=2 v5 callable exact-frame lane, shift≠0 arm: caller `x1 = raVal` preserved
    into `divStackDispatchPostCallableExactFrame`.  Mirrors the dispatched
    `evm_div_n2_lane_shiftNz_v5` but lands the callable exact-frame post via the
    `..._callableExactFrame_uni` wrapper. -/
theorem evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  -- The three runtime borrow flags, in clean `ult (fullDivN2R{2,1}V5 …)` form.
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
  have hdivWord := fullDivN2QuotientWordV5_eq_div_lane_of_shape bltu_2 bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  have hbody := evm_div_n2_stack_pre_to_unified_post_v5_noNop_fromShape sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal x9In x2In
    bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_uni
    bltu_2 bltu_1 bltu_0 sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal x9In x2In
    hdivWord hbody

/-- Shift=0 CALLABLE post bridge: the flag-param full shift=0 path post →
    `divStackDispatchPostCallableExactFrame` (x1 = raVal, x9 = signExtend12 4095)
    with the scratch cell weakened to `memOwn`.  Callable analog of
    `n2_shift0_fullPost_to_divStackDispatchPostV5`: routes through the all-regIs
    `divConcretePostNoX1ExactRegsFrame` (pure `xperm`), then weakens the regs to
    the callable exact frame (instead of all the way to `divStackDispatchPostV5`). -/
theorem n2_shift0_fullPost_to_divStackDispatchPostCallableExactFrame
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (n2Shift0R2 bltu_2 a2 a3 b0 b1).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
        (.x6 ↦ᵣ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
        (.x7 ↦ᵣ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
        (.x2 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1) **
        ((sp + signExtend12 4088) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
        ((sp + signExtend12 4080) ↦ₘ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
        ((sp + signExtend12 4072) ↦ₘ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + 32) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
        ((sp + 40) ↦ₘ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
        ((sp + 48) ↦ₘ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
        ((sp + 56) ↦ₘ (0 : Word))) **
       fullDivN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
         retMem dMem dloMem scratchUn0 scratchMem raVal) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hq
  rw [fullDivN2FrameShift0V5_unfold] at hq
  have hExact :
      (divConcretePostNoX1ExactRegsFrame sp a b (signExtend12 4095) raVal
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1
        (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
        (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1
        (n2Shift0R2 bltu_2 a2 a3 b0 b1).1
        (0 : Word)
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
       ((sp + signExtend12 3936) ↦ₘ n2Shift0ScratchMemF bltu_2 bltu_1 bltu_0 a1 a2 a3 b0 b1 scratchMem)) h := by
    rw [divConcretePostNoX1ExactRegsFrame_unfold,
        evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
        evmWordIs_sp32_limbs_eq sp (EvmWord.div a b)
          (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1
          (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1
          (n2Shift0R2 bltu_2 a2 a3 b0 b1).1 (0 : Word) hdiv0 hdiv1 hdiv2 hdiv3,
        divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
    delta n2Shift0ScratchMemF
    rw [word_add_zero] at hq
    xperm_hyp hq
  exact sepConj_mono
    (fun h hp => by
      rw [divStackDispatchPostCallableExactFrame_unfold]
      exact divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    (fun h hp => memIs_implies_memOwn h hp)
    h hExact

/-- n=2 v5 callable exact-frame lane, shift=0 arm.  Mirrors the dispatched
    `evm_div_n2_lane_shift0_v5` but lands the callable exact-frame post. -/
theorem evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 1)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hb1ge : (b.getLimbN 1).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  have hb1ne : b.getLimbN 1 ≠ 0 := hb1nz
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| (0 : Word) ||| 0 ≠ 0 := by
    intro hz
    exact hb1ne ((BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp
      (BitVec.or_eq_zero_iff.mp hz).1).1).2)
  obtain ⟨bltu_2, hbltu_2⟩ : ∃ x, x = BitVec.ult (0 : Word) (b.getLimbN 1) := ⟨_, rfl⟩
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0
        (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.2.1
        (b.getLimbN 1) := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 1)
        (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.1
        (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.2.1 0 0).2.2.1
        (b.getLimbN 1) := ⟨_, rfl⟩
  have hc2 : bltu_2 = true → BitVec.ult (0 : Word) (b.getLimbN 1) = true :=
    fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false → ¬ BitVec.ult (0 : Word) (b.getLimbN 1) :=
    fun h => by rw [← hbltu_2, h]; decide
  have hc1 : bltu_1 = true →
      BitVec.ult (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0
        (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.2.1 (b.getLimbN 1) = true :=
    fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false →
      ¬ BitVec.ult (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0
        (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.2.1 (b.getLimbN 1) :=
    fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (iterN2V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 1)
        (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.1
        (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.2.1 0 0).2.2.1
        (b.getLimbN 1) = true :=
    fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN2V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 1)
        (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.1
        (iterN2V5 bltu_2 (b.getLimbN 0) (b.getLimbN 1) 0 0 (a.getLimbN 2) (a.getLimbN 3) 0 0 0).2.2.1 0 0).2.2.1
        (b.getLimbN 1) :=
    fun h => by rw [← hbltu_0, h]; decide
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := n2_shift0_div_getLimbN_threaded a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
    bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl hb2z hb3z
    hb1ge hc2 hm2 hc1 hm1 hc0 hm0
  have hpath := evm_div_n2_full_shift0_param_v5_noNop bltu_2 bltu_1 bltu_0 x9In sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
    x2In v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem raVal hbnz' hb1ne hshift_z halign
    hbltu_2 hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n2_shift0_dispatchPre_to_pathEntry sp a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
      raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      rfl rfl rfl rfl rfl rfl hb2z hb3z h hp
  · intro h hq
    exact n2_shift0_fullPost_to_divStackDispatchPostCallableExactFrame bltu_2 bltu_1 bltu_0 sp base a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
      retMem dMem dloMem scratch_un0 scratchMem raVal
      rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- n=2 v5 callable exact-frame lane, shape-level combiner: `by_cases` on the
    normalization shift, delegating to the shift=0 and shift≠0 arms. -/
theorem evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  by_cases hsh : (clzResult (b.getLimbN 1)).1 = 0
  · exact evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2z hb1nz hsh halign
  · exact evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1nz hsh halign

end EvmAsm.Evm64
