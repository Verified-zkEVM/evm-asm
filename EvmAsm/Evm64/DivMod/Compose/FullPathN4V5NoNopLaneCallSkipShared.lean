/-
  Shared declaration home for the n=4 v5/no-NOP dispatch and call-skip lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopFullCallSkip
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLane
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLaneNative

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Bridge the v5 stack-dispatch pre to the n=4 explicit path-entry pre.  `v2`
    (the value in `x2`) is the precomputed normalization shift; the n=4 lane
    supplies `(clzResult b3).2 >>> 63`. -/
theorem n4_dispatchPre_to_pathEntry_v5 (sp : Word) (a b : EvmWord)
    (x1Val v2 v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3) :
    ∀ h,
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        v2 v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) h →
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1) h := by
  intro h hp
  delta divModStackDispatchPreNoX1 at hp
  replace hp := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x1)))) h hp
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp b b0 b1 b2 b3 hb0 hb1 hb2 hb3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
  rw [word_add_zero]
  xperm_hyp hp

open EvmAsm.Rv64

/-- n=4 v5 DIV lane (call+skip branch), from the dispatch pre to
    `divStackDispatchPostV5`, given the quotient-correctness facts. -/
theorem evm_div_n4_lane_callSkip_of_hdiv (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
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
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hpath := evm_div_n4_full_call_skip_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta divStackDispatchPostV5
    unfold fullDivN4CallSkipPostV5 at hq
    exact n4_denormDivPost_frame_to_divStackDispatchPost_v5 sp base a b a0 a1 a2 a3
      _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

open EvmAsm.Rv64

/-- n=4 v5 DIV call-skip lane, with `hdiv` discharged from the word equality;
    takes the runtime call-skip conditions (v4 borrow/semantic + the trial↔v4
    bridge) instead. -/
theorem evm_div_n4_lane_callSkip_of_conds (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrowV5 : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrowV4 : isSkipBorrowN4CallV4Evm a b)
    (hsem : n4CallSkipSemanticHoldsV4 a b)
    (hbridge :
      divKTrialCallV5QHat
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))) =
      div128Quot_v4
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hb3nz' : b.getLimbN 3 ≠ 0 := by rw [hb3]; exact hb3nz
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz' (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hshift_nz' : (clzResult (b.getLimbN 3)).1 ≠ 0 := by rw [hb3]; exact hshift_nz
  have hbnz_lor : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  obtain ⟨hd0, hd1, hd2, hd3⟩ :=
    n4_call_skip_div_mod_getLimbN_v5 a b hb_ne hshift_nz' hborrowV4 hsem hbridge
  rw [ha2, ha3, hb2, hb3] at hd0
  exact evm_div_n4_lane_callSkip_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz_lor hb3nz hshift_nz halign hbltu hborrowV5
    hd0 hd1 hd2 hd3

open EvmAsm.Rv64

/-- n=4 v5 DIV call-skip lane, native: `hdiv` discharged from the v5-native word
    equality (#7640); takes ONLY the v5 skip-borrow `isSkipBorrowN4CallV5`. -/
theorem evm_div_n4_lane_callSkip_of_conds_native (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrowV5 : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hb3nz' : b.getLimbN 3 ≠ 0 := by rw [hb3]; exact hb3nz
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz' (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hshift_nz' : (clzResult (b.getLimbN 3)).1 ≠ 0 := by rw [hb3]; exact hshift_nz
  have hbnz_lor : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hborrowV5' :
      isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]; exact hborrowV5
  obtain ⟨hd0, hd1, hd2, hd3⟩ :=
    n4_call_skip_div_mod_getLimbN_v5_native a b hb_ne hb3nz' hshift_nz' hborrowV5'
  rw [ha2, ha3, hb2, hb3] at hd0
  exact evm_div_n4_lane_callSkip_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz_lor hb3nz hshift_nz halign hbltu hborrowV5
    hd0 hd1 hd2 hd3

end EvmAsm.Evm64
