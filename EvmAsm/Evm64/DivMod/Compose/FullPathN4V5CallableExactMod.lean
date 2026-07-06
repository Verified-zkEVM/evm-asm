/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExactMod

  The v5 n=4 MOD callable exact-frame lane (shift≠0 arm): from
  `divModStackDispatchPreNoX1` (caller return address `raVal` concrete in `x1`) to
  `modStackDispatchPostCallableExactFrame` over `modCode_noNop_v5`.  MOD mirror of
  the DIV `FullPathN4V5CallableExact`, feeding the x1-exact full paths
  (`FullPathN4V5FullExactX1Mod`) through the MOD callable post bridges
  (`FullPathN4V5CallableExactBridgeMod`), discharging the remainder facts from the
  MOD word-lane certs (`N4V5CallSkipModWordLaneNative` / `N4V5CallAddbackModGetLimb`).
  x9In/x2In are free (dead), x1 preserved.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullExactX1Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExactBridgeMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExact
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipModWordLaneNative
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModGetLimb
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddbackMod
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CertOfShape
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallSkipModWordLane
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CallAddbackModWordLane

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000

/-- n=4 v5 MOD callable-exact lane, shift≠0 arm, from the native runtime cert. -/
theorem evm_mod_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hbltu : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hbnz_lor : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  rcases evm_div_n4_shiftNz_cert_of_shape_native a b hb3nz hshift_nz with hbV5 | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch
    obtain ⟨hm0, hm1, hm2, hm3⟩ :=
      n4_call_skip_mod_getLimbN_v5_native a b hb_ne hshift_nz hb3nz hbV5
    have hpath := evm_mod_n4_full_call_skip_spec_v5_noNop_exact_x1 sp base
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      v5 v6 v7 v10 v11Old raVal x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      hbnz_lor hb3nz hshift_nz halign hbltu hbV5
    refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
      cpsTripleWithin_weaken ?_ ?_ hpath
    · intro h hp
      exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
        v5 v6 v7 v10 v11Old x9In
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
        scratchUn0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl h hp
    · intro h hq
      simp only [fullModN4CallSkipPostV5NoX1, zero_add, sepConj_assoc'] at hq
      exact n4_denormModPost_frame_to_modStackDispatchPostCallableExactFrame_v5 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        _ _ _ _ _ _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _
        rfl rfl rfl rfl hm0 hm1 hm2 hm3 h hq
  · -- call+addback branch
    have h_borrow_evm := isAddbackBorrowN4CallV5Evm_of_compose hbV5
    have h_carry2_evm : isAddbackCarry2NzN4CallV5Evm a b := by
      rw [isAddbackCarry2NzN4CallV5Evm_def]
      unfold isAddbackCarry2NzN4CallV5Ab loopBodyN4CallAddbackCarry2NzV5
      unfold isAddbackCarry2NzN4CallV5 at hcarry2
      exact hcarry2
    obtain ⟨hm0, hm1, hm2, hm3⟩ :=
      n4_call_addback_beq_mod_getLimbN_v5 a b hb_ne hb3nz hshift_nz hbltu hsem
        h_borrow_evm h_carry2_evm
    rw [← divKTrialCallV5QHat_eq_div128Quot_v5] at hm0 hm1 hm2 hm3
    have hpath := evm_mod_n4_full_call_addback_spec_v5_noNop_exact_x1 sp base
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      v5 v6 v7 v10 v11Old raVal x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      hbnz_lor hb3nz hshift_nz halign hbltu hbV5 hcarry2
    refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
      cpsTripleWithin_weaken ?_ ?_ hpath
    · intro h hp
      exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
        v5 v6 v7 v10 v11Old x9In
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
        scratchUn0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl h hp
    · intro h hq
      unfold fullModN4CallAddbackPostV5NoX1 at hq
      simp only [zero_add] at hq
      exact n4_denormModPost_frame_to_modStackDispatchPostCallableExactFrame_v5 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        _ _ _ _ _ _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _
        rfl rfl rfl rfl hm0 hm1 hm2 hm3 h (by xperm_hyp hq)

/-- n=4 v5 MOD callable-exact lane, shift=0 arm. -/
theorem evm_mod_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hbnz_lor : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  rcases evm_div_n4_shift0_cert_of_shape a b hb3nz hshift_z with
    ⟨hborrow, _hd0, _hd1, _hd2, _hd3⟩ | ⟨hborrow, hcarry2, _hd0, _hd1, _hd2, _hd3⟩
  · -- call+skip branch
    obtain ⟨hm0, hm1, hm2, hm3⟩ :=
      n4_shift0_call_skip_mod_getLimbN_v5 a b hb_ne hshift_z hborrow
    have hpath := evm_mod_n4_full_call_skip_shift0_spec_v5_noNop_exact_x1 sp base
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      x2In v5 v6 v7 v10 v11Old raVal x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      hbnz_lor hb3nz hshift_z halign hborrow
    refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
      cpsTripleWithin_weaken ?_ ?_ hpath
    · intro h hp
      exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
        v5 v6 v7 v10 v11Old x9In
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
        scratchUn0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl h hp
    · intro h hq
      simp only [fullModN4CallSkipShift0PostV5NoX1, zero_add, sepConj_assoc'] at hq
      exact n4_shift0_post_to_modStackDispatchPostCallableExactFrame_v5 sp a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        _ _ _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _ _ _ _ _
        rfl rfl rfl rfl hm0 hm1 hm2 hm3 h hq
  · -- call+addback branch
    obtain ⟨hm0, hm1, hm2, hm3⟩ :=
      n4_shift0_call_addback_mod_getLimbN_v5 a b hb_ne hshift_z hborrow
    have hpath := evm_mod_n4_full_call_addback_shift0_spec_v5_noNop_exact_x1 sp base
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      x2In v5 v6 v7 v10 v11Old raVal x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      hbnz_lor hb3nz hshift_z halign hborrow hcarry2
    refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
      cpsTripleWithin_weaken ?_ ?_ hpath
    · intro h hp
      exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
        v5 v6 v7 v10 v11Old x9In
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
        scratchUn0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl h hp
    · intro h hq
      have hcarry_nz := n4_shift0_call_addback_first_carry_nz a b hshift_z hborrow
      unfold fullModN4CallAddbackShift0PostV5NoX1 at hq
      simp only [if_neg hcarry_nz, zero_add, sepConj_assoc'] at hq
      exact n4_shift0_post_to_modStackDispatchPostCallableExactFrame_v5 sp a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        _ _ _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _ _ _ _ _
        rfl rfl rfl rfl hm0 hm1 hm2 hm3 h hq

/-- The complete n=4 v5 MOD callable exact-frame lane (both shift arms), at shape:
    only `b.getLimbN 3 ≠ 0` and alignment remain. -/
theorem evm_mod_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  by_cases hsh : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_mod_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign
  · exact evm_mod_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign

end EvmAsm.Evm64
