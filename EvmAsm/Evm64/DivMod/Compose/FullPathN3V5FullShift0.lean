/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FullShift0

  Flag-parameterized full n=3 v5 shift=0 code path `base → nopOff`: the shift=0
  path (`evm_div_n3_to_denorm_shift0_param_v5_noNop`, base→denormOff) ∘ epilogue
  bridge (#7557) ∘ shift=0 DIV epilogue (`evm_div_shift0_epilogue_spec_v5_noNop`,
  denormOff→nopOff).  n=3 analog of `evm_div_n2_full_shift0_param_v5_noNop`.
  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5PathShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5BridgeShift0
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

theorem evm_div_n3_full_shift0_param_v5_noNop (bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 v2 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal x9In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| (0 : Word) ≠ 0) (hb2nz : b2 ≠ 0)
    (hshift_z : (clzResult b2).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult (0 : Word) b2)
    (hbltu_0 : bltu_0 =
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 468) + 12) base (base + nopOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal)))
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
        (.x6 ↦ᵣ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
        ((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
        ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + 32) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
        ((sp + 40) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
        ((sp + 48) ↦ₘ (0 : Word)) **
        ((sp + 56) ↦ₘ (0 : Word))) **
       fullDivN3FrameShift0V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
         retMem dMem dloMem scratchUn0 scratchMem raVal) := by
  have hA := evm_div_n3_to_denorm_shift0_param_v5_noNop bltu_1 bltu_0
    sp base a0 a1 a2 a3 b0 b1 b2 (0 : Word) v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal x9In hbnz rfl hb2nz hshift_z halign
    hbltu_1 hbltu_0
  have hB := evm_div_shift0_epilogue_spec_v5_noNop sp base
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (clzResult b2).1
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (n3Shift0C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2)
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
    (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1
    (0 : Word) (0 : Word)
    b0 b1 b2 0 hshift_z
  have hBf := cpsTripleWithin_frameR
    (fullDivN3FrameShift0V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (by exact fullDivN3FrameShift0V5_pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN3UnifiedPostV5NoX1_shift0_to_epiloguePre bltu_1 bltu_0
        sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
