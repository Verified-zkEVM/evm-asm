/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.BridgeTrue

  True-leading path bridge lemmas from the n=2 unified loop postcondition to
  the bundled denorm precondition and preserved frame.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Branches
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.State

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

theorem preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TFF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hp :
      preloopN2UnifiedPost true false false sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h) :
    (fullDivN2DenormPre true false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2Frame true false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratch_un0) h := by
  delta preloopN2UnifiedPost loopN2UnifiedPost at hp
  simp (config := { decide := true }) only [] at hp
  delta loopN2Iter10Post loopN2MaxPost loopIterPostN2Max at hp
  simp (config := { decide := true }) only
    [loopExitPostN2_j0_eq, n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
      iterN2_true, ite_true, se12_32, se12_40, se12_48, se12_56] at hp
  rw [fullDivN2DenormPre_unfold, fullDivN2Frame_unfold,
    fullDivN2ScratchFinal_unfold, fullDivN2Scratch0_false,
    fullDivN2Scratch1_false, fullDivN2Scratch2_true]
  simp (config := { decide := true }) only
    [fullDivN2Shift_unfold, fullDivN2AntiShift_unfold,
     fullDivN2NormV_unfold, fullDivN2NormU_unfold,
     fullDivN2R2_true, fullDivN2R1_false, fullDivN2R0_false,
     fullDivN2C3_false, n2ScratchRet_unfold, n2ScratchD_unfold,
     n2ScratchDLo_unfold, n2ScratchUn0_unfold,
     se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b1).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set r2 := iterN2Call v0 v1 v2 v3 u2 u3 u4 (0 : Word) (0 : Word) with hr2
  set r1 := iterN2Max v0 v1 v2 v3 u1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1 with hr1
  set r0 := iterN2Max v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 (signExtend12 4095 : Word)
    v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 with hc3
  xperm_hyp hp

theorem preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TFT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hp :
      preloopN2UnifiedPost true false true sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h) :
    (fullDivN2DenormPre true false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2Frame true false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratch_un0) h := by
  delta preloopN2UnifiedPost loopN2UnifiedPost at hp
  simp (config := { decide := true }) only [] at hp
  delta loopN2Iter10Post loopN2MaxCallPost loopIterPostN2Call at hp
  simp (config := { decide := true }) only
    [loopExitPostN2_j0_eq, n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
      iterN2_true, se12_32, se12_40, se12_48, se12_56] at hp
  rw [fullDivN2DenormPre_unfold, fullDivN2Frame_unfold,
    fullDivN2ScratchFinal_unfold, fullDivN2Scratch0_true]
  simp (config := { decide := true }) only
    [fullDivN2Shift_unfold, fullDivN2AntiShift_unfold,
     fullDivN2NormV_unfold, fullDivN2NormU_unfold,
     fullDivN2R2_true, fullDivN2R1_false, fullDivN2R0_true,
     fullDivN2C3_true, n2ScratchRet_unfold, n2ScratchD_unfold,
     n2ScratchDLo_unfold, n2ScratchUn0_unfold,
     se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b1).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set r2 := iterN2Call v0 v1 v2 v3 u2 u3 u4 (0 : Word) (0 : Word) with hr2
  set r1 := iterN2Max v0 v1 v2 v3 u1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1 with hr1
  set r0 := iterN2Call v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v1)
    v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 with hc3
  xperm_hyp hp

theorem preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TTF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hp :
      preloopN2UnifiedPost true true false sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h) :
    (fullDivN2DenormPre true true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2Frame true true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratch_un0) h := by
  delta preloopN2UnifiedPost loopN2UnifiedPost at hp
  simp (config := { decide := true }) only [] at hp
  delta loopN2Iter10Post loopN2CallMaxPost loopIterPostN2Max at hp
  simp (config := { decide := true }) only
    [loopExitPostN2_j0_eq, n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
      iterN2_true, se12_32, se12_40, se12_48, se12_56] at hp
  rw [fullDivN2DenormPre_unfold, fullDivN2Frame_unfold,
    fullDivN2ScratchFinal_unfold, fullDivN2Scratch0_false,
    fullDivN2Scratch1_true]
  simp (config := { decide := true }) only
    [fullDivN2Shift_unfold, fullDivN2AntiShift_unfold,
     fullDivN2NormV_unfold, fullDivN2NormU_unfold,
     fullDivN2R2_true, fullDivN2R1_true, fullDivN2R0_false,
     fullDivN2C3_false, n2ScratchRet_unfold, n2ScratchD_unfold,
     n2ScratchDLo_unfold, n2ScratchUn0_unfold,
     se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b1).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set r2 := iterN2Call v0 v1 v2 v3 u2 u3 u4 (0 : Word) (0 : Word) with hr2
  set r1 := iterN2Call v0 v1 v2 v3 u1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1 with hr1
  set r0 := iterN2Max v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 (signExtend12 4095 : Word)
    v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 with hc3
  xperm_hyp hp

theorem preloopN2UnifiedPost_to_fullDivN2DenormPre_frame_TTT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (h : PartialState)
    (hp :
      preloopN2UnifiedPost true true true sp base a0 a1 a2 a3 b0 b1 b2 b3
        retMem dMem dloMem scratch_un0 h) :
    (fullDivN2DenormPre true true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2Frame true true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratch_un0) h := by
  delta preloopN2UnifiedPost loopN2UnifiedPost at hp
  simp (config := { decide := true }) only [] at hp
  delta loopN2Iter10Post loopN2CallCallPost loopIterPostN2Call at hp
  simp (config := { decide := true }) only
    [loopExitPostN2_j0_eq, n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
      iterN2_true, se12_32, se12_40, se12_48, se12_56] at hp
  rw [fullDivN2DenormPre_unfold, fullDivN2Frame_unfold,
    fullDivN2ScratchFinal_unfold, fullDivN2Scratch0_true]
  simp (config := { decide := true }) only
    [fullDivN2Shift_unfold, fullDivN2AntiShift_unfold,
     fullDivN2NormV_unfold, fullDivN2NormU_unfold,
     fullDivN2R2_true, fullDivN2R1_true, fullDivN2R0_true,
     fullDivN2C3_true, n2ScratchRet_unfold, n2ScratchD_unfold,
     n2ScratchDLo_unfold, n2ScratchUn0_unfold,
     se12_32, se12_40, se12_48, se12_56]
  set shift := (clzResult b1).1 with hshift
  set antiShift := (signExtend12 (0 : BitVec 12) - shift) with hantiShift
  set v0 := b0 <<< (shift.toNat % 64) with hv0
  set v1 := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)) with hv1
  set v2 := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)) with hv2
  set v3 := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)) with hv3
  set u0 := a0 <<< (shift.toNat % 64) with hu0
  set u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)) with hu1
  set u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)) with hu2
  set u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)) with hu3
  set u4 := a3 >>> (antiShift.toNat % 64) with hu4
  set r2 := iterN2Call v0 v1 v2 v3 u2 u3 u4 (0 : Word) (0 : Word) with hr2
  set r1 := iterN2Call v0 v1 v2 v3 u1 r2.2.1 r2.2.2.1 r2.2.2.2.1
    r2.2.2.2.2.1 with hr1
  set r0 := iterN2Call v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1
    r1.2.2.2.2.1 with hr0
  set c3 := (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v1)
    v0 v1 v2 v3 u0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2 with hc3
  xperm_hyp hp

end EvmAsm.Evm64
