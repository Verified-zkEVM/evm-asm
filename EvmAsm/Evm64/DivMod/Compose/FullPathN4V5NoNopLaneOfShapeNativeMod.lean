/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfShapeNativeMod

  The full n=4 v5 MOD lane, UNCONDITIONAL on the n=4 shape — no runtime
  certificates.  Both branches are discharged from the shape:

  * shift=0 → `evm_mod_n4_lane_shift0_v5` (internal borrow case-split, MOD remainder
    facts from the shift=0 skip/addback MOD word lanes);
  * shift≠0 → the native dispatcher `evm_mod_n4_lane_shiftNz_v5_of_cert_native` fed by
    the OP-AGNOSTIC shift≠0 cert-of-shape `evm_div_n4_shiftNz_cert_of_shape_native`
    (reused verbatim from the DIV lane).

  MOD mirror of `evm_div_n4_lane_of_shape_native`: the `lane_n4` obligation of
  `evm_mod_stack_spec_unconditional_of_lanes_v5_mod` discharged from `b3 ≠ 0` (and
  the alignment side condition) alone.  This completes all five n=4 MOD lanes.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNzNativeMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopShiftNzCertOfShape

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The full v5 n=4 MOD lane, discharged from the n=4 shape (`b3 ≠ 0`) and the
    alignment side condition — no runtime certificates. -/
theorem evm_mod_n4_lane_of_shape_native (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_mod_n4_lane_shift0_v5 sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign
  · exact evm_mod_n4_lane_shiftNz_v5_of_cert_native sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign
      (evm_div_n4_shiftNz_cert_of_shape_native a b hb3nz hsh)

end EvmAsm.Evm64
