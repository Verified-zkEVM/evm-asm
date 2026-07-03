/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FullShift0Mod

  Full v5 n=3 MOD code path, shift=0 case (base → nopOff), over `modCode_noNop_v5`:
  the shift=0 preloop+loop (`evm_mod_n3_to_denorm_shift0_param_v5_noNop`) composed
  with the shift=0 MOD epilogue (`evm_mod_shift0_epilogue_spec_v5_noNop`) via a
  MOD-specific loop-post → epilogue-pre bridge.  MOD counterpart of
  `evm_div_n3_full_shift0_param_v5_noNop`: the MOD epilogue reads the un-normalized
  remainder u-cells (sp+4056/4048/4040/4032 = `n3Shift0R0.2.{1,2.1,2.2.1,2.2.2.1}`),
  so the bridge `loopN3UnifiedPostV5NoX1_shift0_to_modEpiloguePre` places those in
  the epilogue's footprint (the DIV bridge buried them in its frame) — proven by
  reusing the DIV bridge and re-partitioning.  The quotient digits
  (sp+4088/4080/4072/4064) are framed through, unread.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5PathShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5BridgeShift0
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- The shift=0 n=3 loop-state frame WITHOUT the four remainder u-cells
    (sp+4056/4048/4040/4032) — those are split out for the MOD shift=0 epilogue.
    Equals `fullDivN3FrameShift0V5` minus those four cells. -/
@[irreducible] def fullModN3FrameShift0V5Rest (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Assertion :=
  let r1 := n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2
  let r0 := n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem
  let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 b2 scratch1 else scratch1
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD1 := if bltu_1 then b2 else dMem
  let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b2 else dloMem
  let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b2 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b2 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.2.1 else scratchUn01)) **
  (sp + signExtend12 3936 ↦ₘ scratchMemF) **
  (.x1 ↦ᵣ raVal)

theorem fullModN3FrameShift0V5Rest_unfold {bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
      retMem dMem dloMem scratchUn0 scratchMem raVal =
    (let r1 := n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2
     let r0 := n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2
     let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem
     let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 b2 scratch1 else scratch1
     let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else retMem
     let scratchD1 := if bltu_1 then b2 else dMem
     let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b2 else dloMem
     let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
     (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b2 else scratchD1)) **
     (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b2 else scratchDLo1)) **
     (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.2.1 else scratchUn01)) **
     (sp + signExtend12 3936 ↦ₘ scratchMemF) **
     (.x1 ↦ᵣ raVal)) := by
  delta fullModN3FrameShift0V5Rest; rfl

theorem fullModN3FrameShift0V5Rest_pcFree {bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    (fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
      retMem dMem dloMem scratchUn0 scratchMem raVal).pcFree := by
  rw [fullModN3FrameShift0V5Rest_unfold]
  cases bltu_1 <;> cases bltu_0 <;>
    simp only [Bool.false_eq_true, if_true, if_false] <;> pcFree

/-- MOD shift=0 loop-post → epilogue-pre bridge (n=3).  Reuses the DIV bridge
    `loopN3UnifiedPostV5NoX1_shift0_to_epiloguePre` and re-partitions: the four
    remainder u-cells (sp+4056/4048/4040/4032) move into the MOD epilogue footprint,
    the quotient output cells split out, leaving `fullModN3FrameShift0V5Rest`. -/
theorem loopN3UnifiedPostV5NoX1_shift0_to_modEpiloguePre
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (h : PartialState)
    (hp : ((loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
              b0 b1 b2 0 a1 a2 a3 0 0 a0
              retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
            (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
             ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
             ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (sp + signExtend12 4056)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (sp + signExtend12 4088)) **
       (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
       (.x10 ↦ᵣ n3Shift0C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
       ((sp + signExtend12 4056) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
       ((sp + signExtend12 4048) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
       ((sp + signExtend12 4040) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
       ((sp + signExtend12 4032) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ (0 : Word))) **
     (((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
       ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word))) **
     fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
       retMem dMem dloMem scratchUn0 scratchMem raVal) h := by
  have hbr := loopN3UnifiedPostV5NoX1_shift0_to_epiloguePre bltu_1 bltu_0
    sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal h hp
  rw [fullDivN3FrameShift0V5_unfold] at hbr
  rw [fullModN3FrameShift0V5Rest_unfold]
  xperm_hyp hbr

/-- Full n=3 MOD code path over `modCode_noNop_v5` (shift = 0): preloop + capped
    loop + MOD remainder epilogue, `base → nopOff`.  The un-normalized remainder
    limbs `n3Shift0R0.2.{1,2.1,2.2.1,2.2.2.1}` land in the output slots
    (sp+32/40/48/56). -/
theorem evm_mod_n3_full_shift0_param_v5_noNop (bltu_1 bltu_0 : Bool)
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
      (modCode_noNop_v5 base)
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
        (.x5 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        (.x6 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        (.x7 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
        ((sp + signExtend12 4056) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        ((sp + signExtend12 4048) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        ((sp + signExtend12 4040) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        ((sp + signExtend12 4032) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        ((sp + 32) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        ((sp + 40) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        ((sp + 48) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        ((sp + 56) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1)) **
       (((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
         ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
         ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4064) ↦ₘ (0 : Word))) **
       fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
         retMem dMem dloMem scratchUn0 scratchMem raVal) := by
  have hA := evm_mod_n3_to_denorm_shift0_param_v5_noNop bltu_1 bltu_0
    sp base a0 a1 a2 a3 b0 b1 b2 (0 : Word) v2 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal x9In hbnz rfl hb2nz hshift_z halign
    hbltu_1 hbltu_0
  have hB := evm_mod_shift0_epilogue_spec_v5_noNop sp base
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
    (clzResult b2).1
    (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (n3Shift0C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2)
    b0 b1 b2 (0 : Word) hshift_z
  have hBf := cpsTripleWithin_frameR
    ((((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
       ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word))) **
      fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
        retMem dMem dloMem scratchUn0 scratchMem raVal)
    (by
      rw [fullModN3FrameShift0V5Rest_unfold]
      cases bltu_1 <;> cases bltu_0 <;>
        simp only [Bool.false_eq_true, if_true, if_false] <;> pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN3UnifiedPostV5NoX1_shift0_to_modEpiloguePre bltu_1 bltu_0
        sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
