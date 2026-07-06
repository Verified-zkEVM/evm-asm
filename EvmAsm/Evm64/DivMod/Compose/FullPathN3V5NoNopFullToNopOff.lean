/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopFullToNopOff

  The full n=3 v5 path from the stack pre-state all the way to the unified post at
  `base + nopOff`, with the carry discharged from shape: composes the loop path
  (`fullDivN3_preloop_loop_unified_exact_x1_scratch_v5_noNop_fromShape`, #7542,
  `base → denormOff`) — bridged per-case through
  `loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_{FF,FT,TF,TT}` (#7545) —
  with the denorm epilogue (`evm_div_n3_denorm_epilogue_bundled_spec_v5_noNop_exact_x1_scratch_frame`,
  #7544, `denormOff → nopOff`), landing `fullDivN3UnifiedPostNoX1V5`.  This is the
  capstone of bead `evm-asm-wbc4i.9.3.3.6`: the direct input to the n=3 post-bridge
  (9.3.3.4).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopFromShape
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenorm
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=3 v5 stack-pre → `fullDivN3UnifiedPostNoX1V5` at `base + nopOff`, carry
    discharged from shape. -/
theorem fullDivN3_preloop_loop_denorm_v5_noNop_fromShape
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hbltu_0 : bltu_0 =
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 468) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      (fullDivN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hShift : fullDivN3Shift b2 ≠ 0 := by delta fullDivN3Shift; exact hshift_nz
  have hDenorm := evm_div_n3_denorm_epilogue_bundled_spec_v5_noNop_exact_x1_scratch_frame
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 scratchMem raVal hShift
  have hLoop := fullDivN3_preloop_loop_unified_exact_x1_scratch_v5_noNop_fromShape
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0
  -- weaken the loop path's post (loop post ** extra-mem) to the denorm-epilogue
  -- precondition via the per-case bridge
  have hLoop' :
      cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 468) base (base + denormOff)
        (divCode_noNop_v5 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
          (.x9 ↦ᵣ x9In) **
          ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
          ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
          ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
          ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
          ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
          ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
          ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
          ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
          ((sp + signExtend12 4024) ↦ₘ u4Old) **
          ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
          ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
          ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
         ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
          (sp + signExtend12 3968 ↦ₘ retMem) **
          (sp + signExtend12 3960 ↦ₘ dMem) **
          (sp + signExtend12 3952 ↦ₘ dloMem) **
          (sp + signExtend12 3944 ↦ₘ scratchUn0) **
          (sp + signExtend12 3936 ↦ₘ scratchMem) **
          (.x1 ↦ᵣ raVal)))
        (fullDivN3DenormPreV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
         fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
           retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ
           fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
         (.x1 ↦ᵣ raVal)) := by
    refine cpsTripleWithin_weaken (fun h hp => hp) ?_ hLoop
    intro h hq
    cases bltu_1 <;> cases bltu_0
    · exact loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_FF
        sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal h hq
    · exact loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_FT
        sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal h hq
    · exact loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_TF
        sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal h hq
    · exact loopN3UnifiedPostV5NoX1_to_fullDivN3DenormPreV5_frame_TT
        sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal h hq
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hLoop' hDenorm

end EvmAsm.Evm64
