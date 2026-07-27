/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExact

  The v5 n=4 DIV callable exact-frame lane: from `divModStackDispatchPreNoX1`
  (caller return address `raVal` concrete in `x1`) to
  `divStackDispatchPostCallableExactFrame` over `divCode_noNop_v5`, both
  normalization-shift arms plus the shape-level combiner.  Mirrors the dispatched
  lanes `evm_div_n4_lane_{shiftNz_v5_of_cert_native,shift0_v5_of_cert}` /
  `evm_div_n4_lane_of_shape_native`, but lands the CALLABLE exact-frame post
  (x1 = raVal preserved) via the callable post bridges
  (`FullPathN4V5CallableExactBridge`), feeding the x1-exact full paths
  (`FullPathN4V5FullExactX1`).  The last per-shape lane needed for
  `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5FullExactX1
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExactBridge
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneAddbackShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopShiftNzCertOfShape
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CertOfShape
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLaneNative
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackWordLane

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- n=4 v5 DIV callable-exact lane (call+skip branch), from the dispatch pre to
    `divStackDispatchPostCallableExactFrame`, given the quotient facts. -/
theorem evm_div_n4_lane_callSkip_of_hdiv_callableExact (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      divKTrialCallV5QHat
        (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
        ((a3 <<< ((clzResult b3).1.toNat % 64)) ||| (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
        ((b3 <<< ((clzResult b3).1.toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))))
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hpath := evm_div_n4_full_call_skip_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old raVal x9In x2In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
      v5 v6 v7 v10 v11Old x9In a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    simp only [fullDivN4CallSkipPostV5NoX1, zero_add, sepConj_assoc'] at hq
    exact n4_denormDivPost_frame_to_divStackDispatchPostCallableExactFrame_v5 sp base a b a0 a1 a2 a3
      _ _ _ _ _ _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- n=4 v5 DIV callable-exact lane (call+addback-beq branch). -/
theorem evm_div_n4_lane_callAddback_of_hdiv_callableExact (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = fullDivN4CallAddbackQuotientV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hpath := evm_div_n4_full_call_addback_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old raVal x9In x2In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
      v5 v6 v7 v10 v11Old x9In a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    simp only [fullDivN4CallAddbackBeqPostV5NoX1, zero_add, sepConj_assoc'] at hq
    exact n4_denormDivPost_frame_to_divStackDispatchPostCallableExactFrame_v5 sp base a b a0 a1 a2 a3
      _ (fullDivN4CallAddbackQuotientV5 a0 a1 a2 a3 b0 b1 b2 b3) _ _ _ _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- n=4 v5 DIV callable-exact lane (shift=0 call+skip branch). -/
theorem evm_div_n4_lane_shift0_callSkip_of_hdiv_callableExact (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word))
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = divKTrialCallV5QHat (0 : Word) a3 b3)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hpath := evm_div_n4_full_call_skip_shift0_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 (x2In) v5 v6 v7 v10 v11Old raVal x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_z halign hborrow
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
      v5 v6 v7 v10 v11Old x9In a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    simp only [fullDivN4CallSkipShift0PostV5NoX1, zero_add, sepConj_assoc'] at hq
    exact n4_shift0_post_to_divStackDispatchPostCallableExactFrame_v5 sp a b a0 a1 a2 a3
      _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _ _ _ _ _ _ _
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- n=4 v5 DIV callable-exact lane (shift=0 call+addback branch). -/
theorem evm_div_n4_lane_shift0_callAddback_of_hdiv_callableExact (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : (if BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat (0 : Word) a3 b3) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat (0 : Word) a3 b3
      let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3) b0 b1 b2 b3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0 b1 b2 b3 ≠ 0)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      fullDivN4CallAddbackShift0QuotientV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hpath := evm_div_n4_full_call_addback_shift0_spec_v5_noNop_exact_x1 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 (x2In) v5 v6 v7 v10 v11Old raVal x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_z halign hborrow hcarry2_nz
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5_exact_x1 sp a b raVal (x2In)
      v5 v6 v7 v10 v11Old x9In a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    simp only [fullDivN4CallAddbackShift0PostV5NoX1, zero_add, sepConj_assoc'] at hq
    exact n4_shift0_post_to_divStackDispatchPostCallableExactFrame_v5 sp a b a0 a1 a2 a3
      _ _ ((signExtend12 4095 : Word)) raVal _ _ _ _ _ _ _ _ _ _
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

/-- n=4 v5 DIV callable-exact lane, shift≠0 arm, from the native runtime cert. -/
theorem evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hbltu : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hbnz_lor : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  rcases evm_div_n4_shiftNz_cert_of_shape_native a b hb3nz hshift_nz with hbV5 | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch
    obtain ⟨hd0, hd1, hd2, hd3⟩ :=
      n4_call_skip_div_mod_getLimbN_v5_native a b hb_ne hb3nz hshift_nz hbV5
    exact evm_div_n4_lane_callSkip_of_hdiv_callableExact sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl hbnz_lor hb3nz hshift_nz halign hbltu hbV5 hd0 hd1 hd2 hd3
  · -- call+addback branch
    obtain ⟨hd0, hd1, hd2, hd3⟩ :=
      n4_call_addback_beq_div_getLimbN_v5 a b hb_ne hb3nz hsem
    rw [← fullDivN4CallAddbackQuotientV5_eq_QOutV5 a b] at hd0
    exact evm_div_n4_lane_callAddback_of_hdiv_callableExact sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl hbnz_lor hb3nz hshift_nz halign hbltu hbV5 hcarry2 hd0 hd1 hd2 hd3

/-- n=4 v5 DIV callable-exact lane, shift=0 arm, from the runtime cert. -/
theorem evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hbnz_lor : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  rcases evm_div_n4_shift0_cert_of_shape a b hb3nz hshift_z with
    ⟨hborrow, hd0, hd1, hd2, hd3⟩ | ⟨hborrow, hcarry2, hd0, hd1, hd2, hd3⟩
  · -- call+skip branch
    exact evm_div_n4_lane_shift0_callSkip_of_hdiv_callableExact sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl hbnz_lor hb3nz hshift_z halign hborrow hd0 hd1 hd2 hd3
  · -- call+addback branch
    exact evm_div_n4_lane_shift0_callAddback_of_hdiv_callableExact sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl hbnz_lor hb3nz hshift_z halign hborrow hcarry2 hd0 hd1 hd2 hd3

/-- The complete n=4 v5 DIV callable exact-frame lane (both shift arms), at shape:
    only `b.getLimbN 3 ≠ 0` and alignment remain. -/
theorem evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_of_shape
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        (x2In) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  by_cases hsh : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shift0
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign
  · exact evm_div_n4_stack_spec_noNop_v5_preNoX1_callableExactFrame_shiftNz
      sp base a b raVal v5 v6 v7 v10 v11Old x9In x2In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign

end EvmAsm.Evm64
