/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipMod

  The n=4 v5 MOD lane, call+skip branch, from the dispatch precondition to
  `modStackDispatchPostV5` over `modCode_noNop_v5`, given the call-skip conditions.
  MOD mirror of `evm_div_n4_lane_callSkip_of_conds`: derives the four
  `(EvmWord.mod a b).getLimbN i` remainder facts via `n4_call_skip_mod_getLimbN_v5`
  (hoisted to top-level context to avoid the whnf blowup of inline derivation),
  then composes the pre-bridge (`n4_dispatchPre_to_pathEntry_v5`), the full
  call+skip path (`evm_mod_n4_full_call_skip_spec_v5_noNop`), and the MOD post
  bridge (`n4_denormModPost_frame_to_modStackDispatchPost_v5`).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopFullCallSkipMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPre
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipModWordLane
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 MOD lane (call+skip branch), from the dispatch pre to
    `modStackDispatchPostV5`, given the call-skip conditions. -/
theorem evm_mod_n4_lane_callSkip_of_conds (sp base : Word) (a b : EvmWord)
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
  -- Convert the borrow-skip cert to the getLimbN form the getLimbN lemma expects
  -- (else `a0 =?= a.getLimbN 0` whnf-loops on the huge application).
  have hborrowV5' : isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
      (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]; exact hborrowV5
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
    n4_call_skip_mod_getLimbN_v5 a b hb_ne hshift_nz' hb3nz' hborrowV4 hborrowV5' hsem hbridge
  simp only [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at hmod0 hmod1 hmod2 hmod3
  have hpath := evm_mod_n4_full_call_skip_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz_lor hb3nz hshift_nz halign hbltu hborrowV5
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta modStackDispatchPostV5
    unfold fullModN4CallSkipPostV5 at hq
    exact n4_denormModPost_frame_to_modStackDispatchPost_v5 sp base a b a0 a1 a2 a3
      _ _ _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq

end EvmAsm.Evm64
