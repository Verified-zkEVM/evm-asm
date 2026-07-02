/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNzMod

  The n=4 v5 MOD lane, shift≠0 case, with the runtime borrow case-split: from the
  stack-dispatch precondition `divModStackDispatchPreNoX1` to `modStackDispatchPostV5`
  over `modCode_noNop_v5`.  MOD mirror of `evm_div_n4_lane_shiftNz_v5_of_cert`:
  dispatches on the SAME op-agnostic runtime certificate `n4ShiftNzLaneRuntimeCertV5`
  (the borrow branch selects call-skip vs. call-addback), applying the MOD call-skip
  lane of conds (`evm_mod_n4_lane_callSkip_of_conds`) on the skip branch and the MOD
  call-addback lane of conds (`evm_mod_n4_lane_callAddback_of_conds`) on the addback
  branch.  The call-trial predicate is discharged from `shift≠0` via
  `isCallTrialN4_of_shift_nz`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNz
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddbackMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 MOD lane, shift≠0 case, dispatching on the runtime borrow certificate.
    MOD mirror of `evm_div_n4_lane_shiftNz_v5_of_cert`. -/
theorem evm_mod_n4_lane_shiftNz_v5_of_cert (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert : n4ShiftNzLaneRuntimeCertV5 a b) :
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
  rcases hcert with ⟨hbV5, hbV4, hsem, hbridge⟩ | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch
    exact evm_mod_n4_lane_callSkip_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hbV4 hsem hbridge
  · -- call+addback branch
    exact evm_mod_n4_lane_callAddback_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hcarry2 hsem

end EvmAsm.Evm64
