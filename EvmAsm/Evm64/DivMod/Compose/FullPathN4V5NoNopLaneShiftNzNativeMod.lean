/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNzNativeMod

  The n=4 v5 MOD lane, shift≠0 case, with a NATIVE runtime certificate: the skip
  branch now demands ONLY the v5 skip-borrow `isSkipBorrowN4CallV5` (consumed by the
  native MOD skip lane `evm_mod_n4_lane_callSkip_of_conds_native`), with NO v4
  borrow, NO v4 semantic `n4CallSkipSemanticHoldsV4`, and NO v5↔v4 trial bridge.
  The addback branch is unchanged (the existing `evm_mod_n4_lane_callAddback_of_conds`).

  MOD mirror of `evm_div_n4_lane_shiftNz_v5_of_cert_native`, dispatching on the SAME
  op-agnostic native cert `n4ShiftNzLaneRuntimeCertV5Native` (defined in the DIV
  file `FullPathN4V5NoNopLaneShiftNzNative`) — so the shape-discharge
  `evm_div_n4_shiftNz_cert_of_shape_native` is reused verbatim.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNzNative
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipOfCondsNativeMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddbackMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 MOD lane, shift≠0 case, dispatching on the NATIVE runtime certificate.
    MOD mirror of `evm_div_n4_lane_shiftNz_v5_of_cert_native`. -/
theorem evm_mod_n4_lane_shiftNz_v5_of_cert_native (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert : n4ShiftNzLaneRuntimeCertV5Native a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hbltu : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  rcases hcert with hbV5 | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch (native: only the v5 borrow)
    exact evm_mod_n4_lane_callSkip_of_conds_native sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5
  · -- call+addback branch (unchanged)
    exact evm_mod_n4_lane_callAddback_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hcarry2 hsem

end EvmAsm.Evm64
