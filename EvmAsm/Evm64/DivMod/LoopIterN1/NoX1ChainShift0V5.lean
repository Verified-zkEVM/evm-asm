/-
  EvmAsm.Evm64.DivMod.LoopIterN1.NoX1ChainShift0V5

  x1-preserving twin of the v5 n=1 shift=0 loop-at-shape theorem
  (`divK_loop_n1_call_unified_v5_shift0_of_shape`): the full v5 n=1 loop at the
  shift=0 inputs over the x1-free pre/post bundles (LoopIterN1/NoX1ChainV5),
  keeping the concrete `x1Val` framed.  Shift=0 counterpart of
  `divK_loop_n1_call_unified_v5_of_shape_preserving_x1`.  Step of the n=1 v5
  callable exact-frame lane (SDIV `.proven` track).
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.NoX1ChainV5
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0LaneRest

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- x1-preserving twin of `divK_loop_n1_call_unified_v5_shift0_of_shape`: the
    full v5 n=1 loop at the shift=0 inputs (`v = (b0,0,0,0)`, `u0 = a3`,
    remaining u-window zero, originals `a2 a1 a0`), keeping the concrete
    `x1Val` framed through the x1-free loop. -/
theorem divK_loop_n1_call_unified_v5_shift0_of_shape_preserving_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     q3Old q2Old q1Old q0Old x1Val : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (a0 a1 a2 a3 b0 : Word)
    (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        b0 0 0 0 a3 0 0 0 0 a2 a1 a0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem **
       (.x1 ↦ᵣ x1Val))
      (loopN1UnifiedPostV5NoX1 sp base
        b0 0 0 0 a3 0 0 0 0 a2 a1 a0 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  refine divK_loop_n1_call_unified_v5_spec_within_noNop_preserving_x1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    b0 0 0 0 a3 0 0 0 0 a2 a1 a0
    q3Old q2Old q1Old q0Old x1Val retMem dMem dloMem scratch_un0 scratchMem base halign
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
