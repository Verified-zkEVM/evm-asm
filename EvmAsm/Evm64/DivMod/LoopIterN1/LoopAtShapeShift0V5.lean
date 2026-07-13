/-
  EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeShift0V5

  The v5 n=1 full loop instantiated at the **shift=0** inputs, with all eight
  per-digit `bltu`/no-borrow hypotheses discharged.  On the shift=0 branch the
  divisor is already top-bit-aligned, so the loop runs on the copy-AU outputs
  `v = (b0, 0, 0, 0)`, `u0 = a3`, `u1 = u2 = u3 = uTop = 0`,
  `u0_orig_2 = a2`, `u0_orig_1 = a1`, `u0_orig_0 = a0` (no normalization).

  This is `divK_loop_n1_call_unified_v5_spec_within_noNop` specialized to those
  inputs, with the eight hypotheses supplied by `N1V5Shift0Lane{FirstDigit,Rest}`.
  The shift=0 counterpart of `divK_loop_n1_call_unified_v5_of_shape`.  Bead
  `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0LaneRest

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divK_loop_n1_call_unified_v5_shift0_of_shape
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (a0 a1 a2 a3 b0 : Word)
    (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        b0 0 0 0 a3 0 0 0 0 a2 a1 a0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1UnifiedPostV5 sp base
        b0 0 0 0 a3 0 0 0 0 a2 a1 a0 scratchMem) := by
  refine divK_loop_n1_call_unified_v5_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    b0 0 0 0 a3 0 0 0 0 a2 a1 a0
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem base halign
    ?hb3 ?hb2 ?hb1 ?hb0 ?ho3 ?ho2 ?ho1 ?ho0
  case hb3 => exact n1v5_shift0_lane_bltu_3 b0 hb0nz hclz
  case hb2 => exact n1v5_shift0_lane_bltu_2 a3 b0 hb0nz hclz
  case hb1 => exact n1v5_shift0_lane_bltu_1 a2 a3 b0 hb0nz hclz
  case hb0 => exact n1v5_shift0_lane_bltu_0 a1 a2 a3 b0 hb0nz hclz
  case ho3 => exact n1v5_shift0_lane_hborrow_3 a3 b0 hb0nz hclz
  case ho2 => exact n1v5_shift0_lane_hborrow_2 a2 a3 b0 hb0nz hclz
  case ho1 => exact n1v5_shift0_lane_hborrow_1 a1 a2 a3 b0 hb0nz hclz
  case ho0 => exact n1v5_shift0_lane_hborrow_0 a0 a1 a2 a3 b0 hb0nz hclz

end EvmAsm.Evm64
