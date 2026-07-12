/-
  EvmAsm.Evm64.DivMod.Spec.N3V5CallableExactMod

  The v5 n=3 MOD callable exact-frame lane: from `divModStackDispatchPreNoX1`
  (with caller return address `raVal` concrete in `x1`, free incoming `x9In`/`x2In`)
  to `modStackDispatchPostCallableExactFrame` over `modCode_noNop_v5`, both
  normalization-shift arms plus the shape-level combiner.  MOD mirror of the DIV
  `Spec/N3V5CallableExact.lean`, landing the callable exact-frame post via the mod
  bridges `fullModN3UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word`
  (shift≠0) and `n3_shift0_fullPost_to_modStackDispatchPostCallableExactFrame`
  (shift=0).  Step toward `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopFullToNopOffMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Shift0Shared
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShift0Mod
import EvmAsm.Evm64.DivMod.Spec.N3V5ConcretePostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.N3V5QuotientLaneShapeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- n=3 v5 MOD callable exact-frame lane, shift≠0 arm: caller `x1 = raVal`
    preserved into `modStackDispatchPostCallableExactFrame`. -/
theorem evm_mod_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
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
  -- The two runtime borrow flags, in clean `ult (fullDivN3R1V5 …)` form.
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (fullDivN3R1V5 bltu_1 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := ⟨_, rfl⟩
  have hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 = true := fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 := fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 = true := fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 := fun h => by rw [← hbltu_0, h]; decide
  -- Remainder correctness from shape (lane form).
  have hdivWord := fullModN3RemainderWordV5_eq_mod_lane_of_shape bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  -- The full entry→nopOff path with carry discharged from shape.
  have hpath := evm_mod_n3_preloop_loop_denorm_v5_noNop_fromShape bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal x9In x2In
    hbnz' hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    rw [divModStackDispatchPreNoX1_unfold] at hp
    rw [show evmWordIs sp a =
        ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
         ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
        from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl]] at hp
    rw [show evmWordIs (sp + 32) b =
        (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
         ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3))
        from by rw [evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl]] at hp
    rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
    simp only [word_add_zero]
    xperm_hyp hp
  · intro h hq
    have hbr := fullModN3UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
      bltu_1 bltu_0 sp base a b retMem dMem dloMem scratch_un0 scratchMem raVal
      hdivWord h hq
    obtain ⟨h1, h2, hd, hu, hframe, hscratch⟩ := hbr
    exact ⟨h1, h2, hd, hu, hframe, memIs_implies_memOwn h2 hscratch⟩

/-- Shift=0 MOD callable bridge: the shift=0 full-path post → callable exact
    frame + concrete scratch cell.  Callable-stop variant of
    `n3_shift0_modPost_to_modStackDispatchPost_v5` (keeps `x1 = raVal`). -/
theorem n3_shift0_fullPost_to_modStackDispatchPostCallableExactFrame
    (bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1)
    (hmod1 : (EvmWord.mod a b).getLimbN 1 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1)
    (hmod2 : (EvmWord.mod a b).getLimbN 2 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1)
    (hmod3 : (EvmWord.mod a b).getLimbN 3 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        (.x6 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        (.x7 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
        ((sp + signExtend12 4056) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        ((sp + signExtend12 4048) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        ((sp + signExtend12 4040) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        ((sp + signExtend12 4032) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        ((sp + 32) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        ((sp + 40) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        ((sp + 48) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        ((sp + 56) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1)) **
       (((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
         ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
         ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4064) ↦ₘ (0 : Word))) **
       fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
         retMem dMem dloMem scratchUn0 scratchMem raVal) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        (if bltu_0 then divKTrialCallV5ScratchOut (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.2.1
            (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.1 b2
            (if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem)
          else if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem))) h := by
  intro h hq
  rw [fullModN3FrameShift0V5Rest_unfold] at hq
  have hExact :
      (modConcretePostNoX1ExactRegsFrame sp a b (signExtend12 4095) raVal
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1 (0 : Word) (0 : Word)
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.2
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.2.2.2 (0 : Word) (0 : Word)
        (clzResult b2).1 (3 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then b2 else if bltu_1 then b2 else dMem)
        (if bltu_0 then divKTrialCallV5DLo b2
          else if bltu_1 then divKTrialCallV5DLo b2 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0 (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.1
          else if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        (if bltu_0 then divKTrialCallV5ScratchOut (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.2.1
            (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.1 b2
            (if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem)
          else if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem))) h := by
    rw [modConcretePostNoX1ExactRegsFrame_unfold,
        evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
        evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
          hmod0 hmod1 hmod2 hmod3,
        divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
    rw [word_add_zero] at hq
    xperm_hyp hq
  rw [modStackDispatchPostCallableExactFrame_unfold]
  exact sepConj_mono_left
    (fun h hp => modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h hExact

/-- n=3 v5 MOD callable exact-frame lane, shift=0 arm. -/
theorem evm_mod_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 2)).1 = 0)
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
  have hb2ge : (b.getLimbN 2).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  obtain ⟨bltu_1, hbltu_1⟩ : ∃ x, x = BitVec.ult (0 : Word) (b.getLimbN 2) := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (iterN3V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) 0
          (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) 0 0).2.2.2.1
        (b.getLimbN 2) := ⟨_, rfl⟩
  have hc1 : bltu_1 = true → BitVec.ult (0 : Word) (b.getLimbN 2) = true :=
    fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false → ¬ BitVec.ult (0 : Word) (b.getLimbN 2) :=
    fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) 0
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) 0 0).2.2.2.1 (b.getLimbN 2) = true :=
    fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) 0
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) 0 0).2.2.2.1 (b.getLimbN 2) :=
    fun h => by rw [← hbltu_0, h]; decide
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ := n3_shift0_mod_getLimbN_threaded a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) bltu_1 bltu_0
    rfl rfl rfl rfl rfl rfl rfl hb3z hb2ge hc1 hm1 hc0 hm0
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| (0 : Word) ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  have hpath := evm_mod_n3_full_shift0_param_v5_noNop bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
    x2In v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem raVal x9In hbnz' hb2nz hshift_z halign
    hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    rw [divModStackDispatchPreNoX1_unfold] at hp
    rw [show evmWordIs sp a =
        ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
         ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
        from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl]] at hp
    rw [show evmWordIs (sp + 32) b =
        (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
         ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3))
        from by rw [evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl]] at hp
    rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
    rw [hb3z] at hp
    simp only [word_add_zero]
    xperm_hyp hp
  · intro h hq
    have hbr := n3_shift0_fullPost_to_modStackDispatchPostCallableExactFrame bltu_1 bltu_0
      sp base a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
      retMem dMem dloMem scratch_un0 scratchMem raVal
      rfl rfl rfl rfl hmod0 hmod1 hmod2 hmod3 h hq
    obtain ⟨h1, h2, hd, hu, hframe, hscratch⟩ := hbr
    exact ⟨h1, h2, hd, hu, hframe, memIs_implies_memOwn h2 hscratch⟩

/-- The complete n=3 v5 MOD callable exact-frame lane (both arms), at shape. -/
theorem evm_mod_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
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
  by_cases hsh : (clzResult (b.getLimbN 2)).1 = 0
  · exact evm_mod_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign
  · exact evm_mod_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign

end EvmAsm.Evm64
