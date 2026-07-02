/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopPreloopBorrowCarry

  Full n=3 v5 path from the stack pre-state to the unified loop post, borrow-carry
  flavour: composes the preloop (`evm_div_n3_to_loopSetup_..._v5_noNop_exact_x1_scratch_frame`,
  `base → loopBodyOff`) with the borrow-dispatched loop instantiation
  (`evm_div_n3_loop_unified_inst_noNop_exact_x1_v5_borrowCarry`, #7539,
  `loopBodyOff → denormOff`), bridged through `loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed`
  (version-agnostic).  The carry is the satisfiable-from-shape
  `loopN3SelectedBorrowCarryV5` bundle (still a hypothesis here; discharged from
  shape in the next step).  v5 mirror of
  `fullDivN3_preloop_loop_unified_exact_x1_scratch_v4_noNop_selectedCarry`.
  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopPreloop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopSelectedBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=3 v5 stack-pre → unified-post, feeding the `loopN3SelectedBorrowCarryV5`
    bundle through the preloop ∘ setup-bridge ∘ borrow-dispatched-loop chain. -/
theorem fullDivN3_preloop_loop_unified_exact_x1_scratch_v5_noNop_borrowCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false =>
        BitVec.ult
          (iterN3Max (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
      | true =>
        BitVec.ult
          (iterWithDoubleAddback
            (divKTrialCallV5QHat
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
              (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
              (fullDivN3NormV b0 b1 b2 b3).2.2.1)
            (fullDivN3NormV b0 b1 b2 b3).1
            (fullDivN3NormV b0 b1 b2 b3).2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (0 : Word)).2.2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hcarry : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0
      (fullDivN3NormV b0 b1 b2 b3).1
      (fullDivN3NormV b0 b1 b2 b3).2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.1
      (fullDivN3NormV b0 b1 b2 b3).2.2.2
      (fullDivN3NormU a0 a1 a2 a3 b2).2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
      (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      (0 : Word)
      (fullDivN3NormU a0 a1 a2 a3 b2).1) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 468) base (base + denormOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
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
      ((loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) := by
  have hPre := evm_div_n3_to_loopSetup_spec_within_v5_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz
  have hLoop := evm_div_n3_loop_unified_inst_noNop_exact_x1_v5_borrowCarry
    bltu_1 bltu_0 sp base
    (fullDivN3Shift b2) (fullDivN3AntiShift b2)
    (fullDivN3NormV b0 b1 b2 b3).1
    (fullDivN3NormV b0 b1 b2 b3).2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.2
    (fullDivN3NormU a0 a1 a2 a3 b2).1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
    (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
    (a0 >>> ((fullDivN3AntiShift b2).toNat % 64)) v11Old jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu_1 (by cases bltu_1 <;> simpa using hbltu_0) hcarry
  have hLoopf := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)))
    (by pcFree) hLoop
  have hBridge := loopSetupPost_to_loopN3PreWithScratchV4NoX1_framed
    sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
  have hPre' := cpsTripleWithin_weaken
    (fun h hp => hp)
    hBridge
    hPre
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

end EvmAsm.Evm64
