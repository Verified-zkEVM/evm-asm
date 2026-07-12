/-
  Shared declaration home for the n=4 v5/no-NOP addback and shift≠0 lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopFullCallAddback
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackWordLane
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

open EvmAsm.Rv64

/-- The n=4 v5 call+addback-beq corrected quotient `q_out` (named; defeq to the
    `q_out` baked into `fullDivN4CallAddbackBeqPostV5`). -/
def fullDivN4CallAddbackQuotientV5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := divKTrialCallV5QHat u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
  else qHat + signExtend12 4095

/-- n=4 v5 DIV lane (call+addback-beq branch), from the dispatch pre to
    `divStackDispatchPostV5`, given the quotient-correctness facts. -/
theorem evm_div_n4_lane_callAddback_of_hdiv (sp base : Word) (a b : EvmWord)
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
    (hborrow : isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = fullDivN4CallAddbackQuotientV5 a0 a1 a2 a3 b0 b1 b2 b3)
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
  have hpath := evm_div_n4_full_call_addback_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta divStackDispatchPostV5
    unfold fullDivN4CallAddbackBeqPostV5 at hq
    exact n4_denormDivPost_frame_to_divStackDispatchPost_v5 sp base a b a0 a1 a2 a3
      _ (fullDivN4CallAddbackQuotientV5 a0 a1 a2 a3 b0 b1 b2 b3) _ _ _ _ _ _ _ _ _ _
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

open EvmAsm.Rv64

/-- The lane-skeleton corrected quotient equals the runtime corrected quotient. -/
theorem fullDivN4CallAddbackQuotientV5_eq_QOutV5 (a b : EvmWord) :
    fullDivN4CallAddbackQuotientV5
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      n4CallAddbackBeqQOutV5 a b := by
  rw [n4CallAddbackBeqQOutV5_raw_unfold]
  unfold fullDivN4CallAddbackQuotientV5
  simp only [divKTrialCallV5QHat_eq_div128Quot_v5]

open EvmAsm.Rv64

/-- n=4 v5 DIV call+addback-beq lane, with `hdiv` discharged from the word
    equality + q_out reconciliation; takes the runtime call-addback conditions
    (the v5 addback borrow/carry2 + the v5 addback semantic) instead. -/
theorem evm_div_n4_lane_callAddback_of_conds (sp base : Word) (a b : EvmWord)
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
    (hborrow : isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b) :
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
  have hbnz_lor : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  obtain ⟨hd0, hd1, hd2, hd3⟩ :=
    n4_call_addback_beq_div_getLimbN_v5 a b hb_ne hb3nz' hsem
  rw [← fullDivN4CallAddbackQuotientV5_eq_QOutV5 a b] at hd0
  rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at hd0
  exact evm_div_n4_lane_callAddback_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz_lor hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
    hd0 hd1 hd2 hd3

open EvmAsm.Rv64

/-- The v5 call-skip trial↔v4 no-wrap bridge in `EvmWord` (`getLimbN`) form: the
    v5 trial quotient equals the v4 trial quotient on the normalized top window.
    This is exactly the `hbridge` premise consumed by `evm_div_n4_lane_callSkip_of_conds`
    (#7612), packaged as a named runtime fact.  Discharged unconditionally on the
    skip branch via #7607 (`divKTrialCallV5QHat_eq_div128Quot_v4_of_no_wrap_of_le`)
    given the no-wrap bounds; here it is carried as part of the runtime certificate. -/
def n4CallSkipBridgeV5Evm (a b : EvmWord) : Prop :=
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
      ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))

/-- Bundled runtime certificate for the n=4 v5 shift≠0 lane: either the runtime
    took the call+skip branch (v5 no-borrow + the v4 borrow/semantic/bridge facts
    the skip lane consumes), or it took the call+addback branch (v5 addback
    borrow + carry2 + the v5 addback semantic).  v5 analog of
    `n4ShiftNzDispatcherBranchRuntimeV4`. -/
def n4ShiftNzLaneRuntimeCertV5 (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   isSkipBorrowN4CallV4Evm a b ∧
   n4CallSkipSemanticHoldsV4 a b ∧
   n4CallSkipBridgeV5Evm a b) ∨
  (isAddbackBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   isAddbackCarry2NzN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                             (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   n4CallAddbackBeqSemanticHoldsV5 a b)

/-- n=4 v5 DIV lane, shift≠0 case, dispatching on the runtime borrow certificate.
    v5 mirror of `evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred`. -/
theorem evm_div_n4_lane_shiftNz_v5_of_cert (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert : n4ShiftNzLaneRuntimeCertV5 a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hbltu : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  rcases hcert with ⟨hbV5, hbV4, hsem, hbridge⟩ | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch
    exact evm_div_n4_lane_callSkip_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hbV4 hsem hbridge
  · -- call+addback branch
    exact evm_div_n4_lane_callAddback_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hcarry2 hsem

open EvmAsm.Rv64

/-- Native bundled runtime certificate for the n=4 v5 shift≠0 lane: either the
    runtime took the call+skip branch (ONLY the v5 skip-borrow), or it took the
    call+addback branch (v5 addback borrow + carry2 + the v5 addback semantic).
    Strictly weaker skip half than `n4ShiftNzLaneRuntimeCertV5` — no v4 facts. -/
def n4ShiftNzLaneRuntimeCertV5Native (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) ∨
  (isAddbackBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   isAddbackCarry2NzN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                             (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   n4CallAddbackBeqSemanticHoldsV5 a b)

/-- n=4 v5 DIV lane, shift≠0 case, dispatching on the NATIVE runtime certificate.
    v5-native mirror of `evm_div_n4_lane_shiftNz_v5_of_cert`. -/
theorem evm_div_n4_lane_shiftNz_v5_of_cert_native (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert : n4ShiftNzLaneRuntimeCertV5Native a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hbltu : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  rcases hcert with hbV5 | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch (native: only the v5 borrow)
    exact evm_div_n4_lane_callSkip_of_conds_native sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5
  · -- call+addback branch (unchanged)
    exact evm_div_n4_lane_callAddback_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hcarry2 hsem

end EvmAsm.Evm64
