/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnifiedBorrowCarry

  Borrow-dispatched unified n=2 v5 loop: takes `loopN2SelectedBorrowCarryV5` (the
  satisfiable-from-shape carry bundle, #7448) instead of the unsatisfiable
  `loopN2SelectedCarryV5`, and dispatches the 8 `bltu³` cases to the from_source
  `_borrowCarry` combos (#7436/44/45/46/47), extracting the three per-digit
  borrow-conditional carries from the bundle in each arm.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefsBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopDispatchShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCCBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMMBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCMBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMTBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMTMBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMTTBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboTMMBorrowCarry
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboTMTBorrowCarry

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedBorrowCarryV5 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  · -- FFF = MMM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_false] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxMaxMaxSourceFinalPostNoX1V5_unfold, r2MMTN2V5_eq, r1MMTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MMTN2V5_eq, r1MMTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem hb2 hc2 hb1 hc1 hb0 hc0)
  · -- FFT = MMC
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_false] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxMaxCallSourceFinalPostNoX1V5_unfold, r2MMTN2V5_eq, r1MMTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MMTN2V5_eq, r1MMTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_max_call_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)
  · -- FTF = MCM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : ¬BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxCallMaxSourceFinalPostNoX1V5_unfold, r2MTTN2V5_eq, r1MTTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MTTN2V5_eq, r1MTTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_call_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)
  · -- FTT = MCC
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxCallCallSourceFinalPostNoX1V5_unfold, r2MTTN2V5_eq, r1MTTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MTTN2V5_eq, r1MTTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_call_call_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)
  · -- TFF = TMM (call-max-max)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallMaxMaxSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1TMMN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1TMMN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_max_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)
  · -- TFT = TMT (call-max-call)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallMaxCallSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1TMMN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1TMMN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_max_call_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)
  · -- TTF = CCM (call-call-max)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : ¬BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_true] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallCallMaxSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1CCCN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1CCCN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_call_max_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)
  · -- TTT = CCC (all call)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    unfold loopN2SelectedBorrowCarryV5 at hcarry
    simp only [loopN2IterSelectedV5_true] at hcarry
    obtain ⟨hc2, hc1, hc0⟩ := hcarry
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallCallCallSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1CCCN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1CCCN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_call_call_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb2 hc2 hb1 hc1 hb0 hc0)

end EvmAsm.Evm64
