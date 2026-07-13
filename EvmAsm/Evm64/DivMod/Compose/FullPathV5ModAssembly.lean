/-
  EvmAsm.Evm64.DivMod.Compose.FullPathV5ModAssembly

  The v5 MOD unconditional spec: instantiates the 5-lane scaffold
  `evm_mod_stack_spec_unconditional_of_lanes_v5_mod` with the shape-uniform shift
  `v2 := divDispatchShiftX2 b` and discharges ALL FIVE lanes (bzero / n1 / n2 / n3
  / n4) from the proven MOD lanes, reconciling the uniform `v2` to each lane's
  pinned `clzResult (top limb)` via `divDispatchShiftX2_n{1,2,3,4}`.

  MOD mirror of `evm_div_stack_spec_unconditional_v5_div_of_n4lane`
  (FullPathV5DivAssembly).  Unlike the DIV assembly — which took the n4 lane as a
  hypothesis — every MOD lane is now proven, so the result
  `evm_mod_stack_spec_unconditional_v5_mod` is fully unconditional (only the
  alignment side condition remains).  The last composition step before the v6
  embedding.
-/

import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod
import EvmAsm.Evm64.DivMod.Spec.DivDispatchShift
import EvmAsm.Evm64.DivMod.Compose.FullPathV5BzeroMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShift0Mod
import EvmAsm.Evm64.DivMod.ModN2V5ShiftShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfShapeNativeMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 MOD unconditional spec: with the uniform shift `divDispatchShiftX2 b`
    in `x2`, the full dispatch triple holds for every divisor shape — all five
    lanes are discharged from the proven MOD lanes. -/
theorem evm_mod_stack_spec_unconditional_v5_mod
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  refine evm_mod_stack_spec_unconditional_of_lanes_v5_mod sp base a b
    (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    exact evm_mod_bzero_lane_v5 sp base a b
      (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hbz
  case n1 =>
    intro hshape
    rw [divDispatchShiftX2_n1 hshape]
    have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
      intro heq
      exact hshape.2.2.2.2
        (BitVec.or_eq_zero_iff.mp
          (BitVec.or_eq_zero_iff.mp
            (BitVec.or_eq_zero_iff.mp heq).1).1).1
    exact evm_mod_n1_lane_v5 sp base a b raVal v5 v6 v7 v10 v11
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl
      hbnz hshape.2.1 hshape.2.2.1 hshape.2.2.2.1 halign
  case n2 =>
    intro hshape
    rw [divDispatchShiftX2_n2 hshape]
    exact evm_mod_n2_lane_complete_v5 sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem
      hshape.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2 halign
  case n3 =>
    intro hshape
    rw [divDispatchShiftX2_n3 hshape]
    exact evm_mod_n3_lane_v5 sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hshape.2.1 hshape.2.2 halign
  case n4 =>
    intro hshape
    rw [divDispatchShiftX2_n4 hshape]
    exact evm_mod_n4_lane_of_shape_native sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hshape.2 halign

end EvmAsm.Evm64
