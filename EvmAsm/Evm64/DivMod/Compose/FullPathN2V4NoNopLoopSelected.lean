/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopLoopSelected

  Selected-carry n=2 v4/no-NOP unified loop source theorem.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopLoopUnified

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-carry variant of
    `divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop`.
    This is the lower-loop replacement for the false universal `Carry2NzAll`
    package: callers provide only the three carry facts selected by the actual
    `bltu_2 × bltu_1 × bltu_0` path. -/
theorem divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
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
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
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
          (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    cpsTripleWithin 672 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV4NoX1 bltu_2 bltu_1 bltu_0 sp base
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
    have hconds := loopN2MaxMaxMaxSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxMaxMaxSourceFinalPostNoX1_unfold, r2MMMN2V4_eq, r1MMMN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MMMN2V4_eq, r1MMMN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem hconds)
  · -- FFT = MMT
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2MaxMaxCallSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxMaxCallSourceFinalPostNoX1_unfold, r2MMTN2V4_eq, r1MMTN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MMTN2V4_eq, r1MMTN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_max_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTF = MTM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : ¬BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2MaxCallMaxSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxCallMaxSourceFinalPostNoX1_unfold, r2MTMN2V4_eq, r1MTMN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MTMN2V4_eq, r1MTMN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_call_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTT = MTT
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2MaxCallCallSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxCallCallSourceFinalPostNoX1_unfold, r2MTTN2V4_eq, r1MTTN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MTTN2V4_eq, r1MTTN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_call_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFF = TMM
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2CallMaxMaxSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallMaxMaxSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1TMMN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1TMMN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_max_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFT = TMT
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2CallMaxCallSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallMaxCallSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1TMTN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1TMTN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_max_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTF = CCM
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : ¬BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2CallCallMaxSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallCallMaxSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1CCCN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1CCCN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_call_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTT = CCC
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2CallCallCallSourceConds_of_selectedCarryV4
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallCallCallSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1CCCN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1CCCN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_call_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)

/-- Instantiate the selected-carry v4/no-NOP n=2 unified loop with explicit
    normalized values. -/
theorem evm_div_n2_loop_unified_inst_noNop_exact_x1_v4_selectedCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift v0' v1' v2' v3' u0S u1S u2S u3S u4_s : Word)
    (v10_val v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u4_s v1')
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1'
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
          v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1')
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1')
    (hcarry : loopN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S) :
    cpsTripleWithin 672 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jMem (2 : Word) shift u0S v10_val v11Old antiShift
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
        u1S u0S (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV4NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
  (simp only at hbltu_0 hbltu_1 hbltu_2;
   exact divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry
     _ _ _ sp base
     jMem (2 : Word) shift u0S v10_val v11Old antiShift
     v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
     (0 : Word) (0 : Word) (0 : Word) raVal
     retMem dMem dloMem scratch_un0 scratchMem
     halign hbltu_2 hbltu_1 hbltu_0 hcarry)

end EvmAsm.Evm64
