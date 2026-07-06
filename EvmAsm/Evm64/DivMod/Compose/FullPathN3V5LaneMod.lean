/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneMod

  The full v5 n=3 MOD lane: combines the shift≠0 and shift=0 halves by
  `by_cases (clzResult (b.getLimbN 2)).1 = 0`.  MOD mirror of `evm_div_n3_lane_v5`.
  One lane theorem over `modCode_noNop_v5` → `modStackDispatchPostV5`, the n=3
  entry in the 5-lane MOD dispatch.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShift0Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The full v5 n=3 MOD lane (both shift arms). -/
theorem evm_mod_n3_lane_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 2)).1 = 0
  · exact evm_mod_n3_lane_shift0_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign
  · exact evm_mod_n3_lane_shiftNz_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hb3z hb2nz hsh halign

end EvmAsm.Evm64
