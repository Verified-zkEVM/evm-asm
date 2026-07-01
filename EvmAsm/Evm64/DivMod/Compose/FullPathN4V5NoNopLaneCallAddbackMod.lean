/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddbackMod

  The n=4 v5 MOD lane, call+addback branch, from the dispatch precondition to
  `modStackDispatchPostV5` over `modCode_noNop_v5`, given the call-addback
  conditions.  MOD mirror of `evm_div_n4_lane_callAddback_of_conds`: derives the
  four carry-selected `(EvmWord.mod a b).getLimbN i` remainder facts via the
  combined `n4_call_addback_beq_mod_getLimbN_v5` (hoisted to avoid the whnf
  blowup of inline derivation), bridges the trial quotient `div128Quot_v5` to the
  code-level `divKTrialCallV5QHat`, then composes the pre-bridge
  (`n4_dispatchPre_to_pathEntry_v5`), the full call+addback path
  (`evm_mod_n4_full_call_addback_spec_v5_noNop`), and the MOD post bridge
  (`n4_denormModPost_frame_to_modStackDispatchPost_v5`).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopFullCallAddbackMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPre
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackModGetLimb
import EvmAsm.Evm64.DivMod.Spec.N4Carry2ComposeBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- n=4 v5 MOD lane (call+addback branch), from the dispatch pre to
    `modStackDispatchPostV5`, given the call-addback conditions. -/
theorem evm_mod_n4_lane_callAddback_of_conds (sp base : Word) (a b : EvmWord)
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
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hb3nz' : b.getLimbN 3 ≠ 0 := by rw [hb3]; exact hb3nz
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz' (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hshift_nz' : (clzResult (b.getLimbN 3)).1 ≠ 0 := by rw [hb3]; exact hshift_nz
  have hbnz_lor : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  -- Convert the runtime conditions to the getLimbN / Evm forms the getLimbN
  -- lemma expects (else `a0 =?= a.getLimbN 0` whnf-loops on the huge application).
  have hborrow' : isAddbackBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
      (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]; exact hborrow
  have hcarry2' : isAddbackCarry2NzN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
      (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]; exact hcarry2_nz
  have hbltu' : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [ha3, hb2, hb3]; exact hbltu
  have h_borrow_evm := isAddbackBorrowN4CallV5Evm_of_compose hborrow'
  have h_carry2_evm : isAddbackCarry2NzN4CallV5Evm a b := by
    rw [isAddbackCarry2NzN4CallV5Evm_def]
    unfold isAddbackCarry2NzN4CallV5Ab loopBodyN4CallAddbackCarry2NzV5
    unfold isAddbackCarry2NzN4CallV5 at hcarry2'
    exact hcarry2'
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
    n4_call_addback_beq_mod_getLimbN_v5 a b hb_ne hb3nz' hshift_nz' hbltu' hsem
      h_borrow_evm h_carry2_evm
  -- Bridge the trial quotient `div128Quot_v5` → `divKTrialCallV5QHat` and the
  -- limb accessors → raw limbs, so the facts match `fullModN4CallAddbackPostV5`.
  rw [← divKTrialCallV5QHat_eq_div128Quot_v5] at hmod0 hmod1 hmod2 hmod3
  simp only [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at hmod0 hmod1 hmod2 hmod3
  have hpath := evm_mod_n4_full_call_addback_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz_lor hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta modStackDispatchPostV5
    unfold fullModN4CallAddbackPostV5 at hq
    apply n4_denormModPost_frame_to_modStackDispatchPost_v5 sp base a b a0 a1 a2 a3
      _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h
    xperm_hyp hq

end EvmAsm.Evm64
