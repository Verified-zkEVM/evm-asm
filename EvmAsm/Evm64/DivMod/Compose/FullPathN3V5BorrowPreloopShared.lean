/- Shared declaration home for the n=3 MOD unified loop, selected loop, and preloop. -/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopDefsBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnifiedBorrowCarryCasesMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopPreloopMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Borrow-dispatched n=3 v5 unified loop: the carries come from the
    satisfiable-from-shape `loopN3SelectedBorrowCarryV5` bundle (borrow-conditional
    per digit), dispatched to the per-case unified-post `_borrowCarry` wrappers. -/
theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · -- max × max
    have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 :
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        ¬BitVec.ult r1.2.2.2.1 v2 := by
      simp only at hbltu_0 ⊢; rw [← hbltu_0]; decide
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_false_eq_max] at hcarry
    rw [if_neg (by decide), if_neg (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_maxmax_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem hb1 hc1 hb0 hc0
  · -- max × call
    have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 :
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        BitVec.ult r1.2.2.2.1 v2 := by
      simp only at hbltu_0 ⊢; exact hbltu_0.symm
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_false_eq_max] at hcarry
    rw [if_neg (by decide), if_pos (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_maxcall_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0
  · -- call × max
    have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        ¬BitVec.ult r1.2.2.2.1 v2 := by
      simp only at hbltu_0 ⊢; rw [← hbltu_0]; decide
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_true_eq] at hcarry
    rw [if_pos (by decide), if_neg (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_callmax_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0
  · -- call × call
    have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; exact hbltu_0.symm
    unfold loopN3SelectedBorrowCarryV5 at hcarry
    simp only [iterN3V5_true_eq] at hcarry
    rw [if_pos (by decide), if_pos (by decide)] at hcarry
    obtain ⟨hc1, hc0⟩ := hcarry
    exact divK_loop_n3_unified_callcall_borrowCarry_modCode sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hb1 hc1 hb0 hc0


open EvmAsm.Rv64

/-- Borrow-conditional instantiation of the v5 no-NOP exact-`x1` n=3 loop with
    explicit normalized values (the form the preloop composition consumes), feeding
    the `loopN3SelectedBorrowCarryV5` bundle. -/
theorem evm_mod_n3_loop_unified_inst_noNop_exact_x1_v5_borrowCarry_modCode
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u4 u3 b2')
            b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry : loopN3SelectedBorrowCarryV5 bltu_1 bltu_0
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) :=
  divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_modCode_borrowCarry
    bltu_1 bltu_0 sp base jMem (3 : Word) shift u0 v10Old v11Old antiShift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hbltu_0 hcarry


open EvmAsm.Rv64

/-- Full n=3 v5 stack-pre → unified-post, feeding the `loopN3SelectedBorrowCarryV5`
    bundle through the preloop ∘ setup-bridge ∘ borrow-dispatched-loop chain. -/
theorem evm_mod_n3_preloop_loop_unified_exact_x1_scratch_v5_noNop_borrowCarry
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
      (modCode_noNop_v5 base)
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
  have hPre := evm_mod_n3_to_loopSetup_spec_within_v5_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In x2In
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2nz hshift_nz
  have hLoop := evm_mod_n3_loop_unified_inst_noNop_exact_x1_v5_borrowCarry_modCode
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
