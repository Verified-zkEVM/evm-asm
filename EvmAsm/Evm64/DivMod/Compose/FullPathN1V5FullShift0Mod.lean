/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullShift0Mod

  Full v5 n=1 MOD code path, shift=0 case (base → nopOff), over `modCode_noNop_v5`:
  the shift=0 preloop+loop (`evm_mod_n1_to_denorm_shift0_spec_v5_noNop`) composed
  with the shift=0 MOD epilogue (`evm_mod_shift0_epilogue_spec_v5_noNop`) via a
  MOD-specific loop-post → epilogue-pre bridge.  MOD counterpart of
  `evm_div_n1_full_shift0_spec_v5_noNop`: the MOD epilogue reads the un-normalized
  remainder u-cells (sp+4056/4048/4040/4032 = `R0.2.{1,2.1,2.2.1,2.2.2.1}`), so the
  bridge `loopN1UnifiedPostV5_shift0_to_modEpiloguePre` exposes those in the
  epilogue's footprint (the DIV bridge buried them in its frame).  The quotient
  digits (sp+4088/4080/4072/4064) are framed through, unread.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5BridgeShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenormShift0Mod
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

attribute [local irreducible] EvmWord.val256 div128Quot_v5 iterWithDoubleAddback mulsubN4 clzResult

/-- The shift=0 loop-state frame WITHOUT the four remainder u-cells
    (sp+4056/4048/4040/4032) and WITHOUT the quotient output cells
    (sp+4088/4080/4072/4064) — those are split out for the MOD shift=0 epilogue. -/
@[irreducible] def fullModN1FrameShift0V5Rest (sp base a0 a1 a2 a3 b0 scratchMem : Word) : Assertion :=
  let R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0
  let R2 := fullN1S2 b0 0 0 0 a3 0 0 0 0 a2
  let R1 := fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1
  let R0 := fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b0) **
  ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b0) **
  ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a0) **
  ((sp + signExtend12 3936) ↦ₘ
    divKTrialCallV5ScratchOut R1.2.1 a0 b0
      (divKTrialCallV5ScratchOut R2.2.1 a1 b0
        (divKTrialCallV5ScratchOut R3.2.1 a2 b0
          (divKTrialCallV5ScratchOut 0 a3 b0 scratchMem)))) **
  regOwn .x1

theorem fullModN1FrameShift0V5Rest_unfold {sp base a0 a1 a2 a3 b0 scratchMem : Word} :
    fullModN1FrameShift0V5Rest sp base a0 a1 a2 a3 b0 scratchMem =
    (let R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0
     let R2 := fullN1S2 b0 0 0 0 a3 0 0 0 0 a2
     let R1 := fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1
     let R0 := fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
     ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b0) **
     ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b0) **
     ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a0) **
     ((sp + signExtend12 3936) ↦ₘ
       divKTrialCallV5ScratchOut R1.2.1 a0 b0
         (divKTrialCallV5ScratchOut R2.2.1 a1 b0
           (divKTrialCallV5ScratchOut R3.2.1 a2 b0
             (divKTrialCallV5ScratchOut 0 a3 b0 scratchMem)))) **
     regOwn .x1) := by
  delta fullModN1FrameShift0V5Rest; rfl

/-- MOD shift=0 loop-post → epilogue-pre bridge.  Mirror of
    `loopN1UnifiedPostV5_shift0_to_epiloguePre` (same proof), but the four
    remainder u-cells (sp+4056/4048/4040/4032) are placed in the explicit
    epilogue footprint (the MOD epilogue reads them) and the quotient output cells
    are split out separately, leaving `fullModN1FrameShift0V5Rest`. -/
theorem loopN1UnifiedPostV5_shift0_to_modEpiloguePre
    (sp base a0 a1 a2 a3 b0 scratchMem : Word) (h : PartialState)
    (hp : (loopN1UnifiedPostV5 sp base b0 0 0 0 a3 0 0 0 0 a2 a1 a0 scratchMem **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)) h) :
    (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (sp + signExtend12 4056)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (sp + signExtend12 4088)) **
       (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
       (.x10 ↦ᵣ (mulsubN4
            (div128Quot_v5 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
            b0 0 0 0 a0
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1).2.2.2.2) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
       ((sp + signExtend12 4056) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
       ((sp + signExtend12 4048) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
       ((sp + signExtend12 4040) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
       ((sp + signExtend12 4032) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) **
     (((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
       ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
       ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
       ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
     fullModN1FrameShift0V5Rest sp base a0 a1 a2 a3 b0 scratchMem) h := by
  rw [fullModN1FrameShift0V5Rest_unfold]
  delta loopN1UnifiedPostV5 loopN1Iter210PostV5 loopN1Iter10PostV5 loopIterPostN1V5
    loopIterPostN1CallV5 at hp
  dsimp only [] at hp
  rw [loopExitPostN1_j0_eq] at hp
  rw [← iterN1Call_v5_unfoldU'] at hp
  delta fullN1S0 fullN1S1 fullN1S2
  dsimp only []
  simp only [n1_ub3_off4064, n1_qa3, n2_ub2_off4064, n2_qa2,
      n3_ub1_off4064, n3_qa1, iterN1V5_true, if_true,
      se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp ⊢
  set R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0 with hR3
  set R2 := iterN1Call_v5 b0 0 0 0 a2 R3.2.1 R3.2.2.1 R3.2.2.2.1 R3.2.2.2.2.1 with hR2
  set R1 := iterN1Call_v5 b0 0 0 0 a1 R2.2.1 R2.2.2.1 R2.2.2.2.1 R2.2.2.2.2.1 with hR1
  set R0 := iterN1Call_v5 b0 0 0 0 a0 R1.2.1 R1.2.2.1 R1.2.2.2.1 R1.2.2.2.2.1 with hR0
  xperm_chunked hp

/-- Full n=1 MOD code path over `modCode_noNop_v5` (shift = 0): preloop + capped
    loop + MOD remainder epilogue, `base → nopOff`.  The un-normalized remainder
    limbs `R0.2.{1,2.1,2.2.1,2.2.2.1}` land in the output slots (sp+32/40/48/56). -/
theorem evm_mod_n1_full_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 632) + 12) base (base + nopOff)
      (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
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
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** regOwn .x1)
      (((.x12 ↦ᵣ (sp + 32)) **
         (.x5 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         (.x6 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         (.x7 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
         ((sp + signExtend12 4056) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         ((sp + signExtend12 4048) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         ((sp + signExtend12 4040) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         ((sp + signExtend12 4032) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         ((sp + 32) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         ((sp + 40) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         ((sp + 48) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         ((sp + 56) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1)) **
        (((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
          ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
          ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
          ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
        fullModN1FrameShift0V5Rest sp base a0 a1 a2 a3 b0 scratchMem) := by
  have hA := evm_mod_n1_to_denorm_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_z halign
  have hB := evm_mod_shift0_epilogue_spec_v5_noNop sp base
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1
    (clzResult b0).1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (mulsubN4
        (div128Quot_v5 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
        b0 0 0 0 a0
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1).2.2.2.2
    b0 (0 : Word) (0 : Word) (0 : Word) hshift_z
  have hBf := cpsTripleWithin_frameR
    ((((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
       ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
       ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
       ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
      fullModN1FrameShift0V5Rest sp base a0 a1 a2 a3 b0 scratchMem)
    (by rw [fullModN1FrameShift0V5Rest_unfold]; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN1UnifiedPostV5_shift0_to_modEpiloguePre sp base a0 a1 a2 a3 b0 scratchMem h hp
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
