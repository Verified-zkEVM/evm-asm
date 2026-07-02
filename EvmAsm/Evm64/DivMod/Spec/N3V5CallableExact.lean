/-
  EvmAsm.Evm64.DivMod.Spec.N3V5CallableExact

  The v5 n=3 DIV callable exact-frame lane: from `divModStackDispatchPreNoX1`
  (with caller return address `raVal` concrete in `x1`) to
  `divStackDispatchPostCallableExactFrame` over `divCode_noNop_v5`, both
  normalization-shift arms plus the shape-level combiner.  Mirrors the
  dispatched lanes `evm_div_n3_lane_{shiftNz,shift0}_v5` /`evm_div_n3_lane_v5`
  verbatim, but lands the CALLABLE exact-frame post (x1 = raVal preserved) via
  `fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word`
  (shift≠0) and `n3_shift0_fullPost_to_divStackDispatchPostCallableExactFrame`
  (shift=0), weakening only the trial scratch cell to `memOwn`.  n=3 analog of
  `evm_div_n1_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape` and the
  n2 `N2V5CallableExact` wrapper.  Step toward `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopFullToNopOff
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FullShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5DivLimbThreadedShift0
import EvmAsm.Evm64.DivMod.Spec.N3V5ConcretePostBridge
import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0PostBridgeCallable
import EvmAsm.Evm64.DivMod.Spec.N3V5QuotientLaneShape
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- n=3 v5 callable exact-frame lane, shift≠0 arm: caller `x1 = raVal` preserved
    into `divStackDispatchPostCallableExactFrame`. -/
theorem evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
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
  -- The per-digit `bltu` path matches, from the clean flag definitions.
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
  -- Quotient correctness from shape (lane form).
  have hdivWord := fullDivN3QuotientWordV5_eq_div_lane_of_shape bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  -- The limb-`or` form of `b ≠ 0`, derived from `b2 ≠ 0`.
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  -- The full entry→nopOff path with carry discharged from shape.
  have hpath := fullDivN3_preloop_loop_denorm_v5_noNop_fromShape bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal x9In
    hbnz' hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · -- pre-adapter: the dispatch pre unfolds to the explicit stack pre-state.
    intro h hp
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
  · -- post bridge: callable exact frame, scratch cell weakened to memOwn.
    intro h hq
    have hbr := fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
      bltu_1 bltu_0 sp base a b retMem dMem dloMem scratch_un0 scratchMem raVal
      hdivWord h hq
    obtain ⟨h1, h2, hd, hu, hframe, hscratch⟩ := hbr
    exact ⟨h1, h2, hd, hu, hframe, memIs_implies_memOwn h2 hscratch⟩

/-- n=3 v5 callable exact-frame lane, shift=0 arm. -/
theorem evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 2)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hb2ge : (b.getLimbN 2).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  -- canonical flags (clean ult, threaded raw-window iterN3V5 form)
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
  -- quotient correctness from shape (n3Shift0R* form)
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := n3_shift0_div_getLimbN_threaded a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) bltu_1 bltu_0
    rfl rfl rfl rfl rfl rfl rfl hb3z hb2ge hc1 hm1 hc0 hm0
  -- limb-`or` form of `b ≠ 0`, from `b2 ≠ 0`
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| (0 : Word) ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  -- the flag-param full shift=0 path
  have hpath := evm_div_n3_full_shift0_param_v5_noNop bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
    ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem raVal x9In hbnz' hb2nz hshift_z halign
    hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · -- pre-adapter: the dispatch pre unfolds to the explicit stack pre-state.
    intro h hp
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
  · -- post bridge: callable exact frame, scratch cell weakened to memOwn.
    intro h hq
    have hbr := n3_shift0_fullPost_to_divStackDispatchPostCallableExactFrame bltu_1 bltu_0
      sp base a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
      retMem dMem dloMem scratch_un0 scratchMem raVal
      rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3 h hq
    obtain ⟨h1, h2, hd, hu, hframe, hscratch⟩ := hbr
    exact ⟨h1, h2, hd, hu, hframe, memIs_implies_memOwn h2 hscratch⟩

/-- The complete n=3 v5 callable exact-frame lane (both normalization-shift
    arms), at shape: only `b3 = 0`, `b2 ≠ 0`, and alignment remain. -/
theorem evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  by_cases hsh : (clzResult (b.getLimbN 2)).1 = 0
  · exact evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
      sp base a b raVal v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign
  · exact evm_div_n3_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
      sp base a b raVal v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign

end EvmAsm.Evm64
