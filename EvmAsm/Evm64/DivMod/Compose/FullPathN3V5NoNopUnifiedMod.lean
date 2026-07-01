/- n=3 MOD unified loop dispatcher over modCode_noNop_v5. Reuses the code-agnostic
   defs from FullPathN3V5NoNopUnified; only the modCode theorem differs. -/
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCallCombosMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopMaxCombosMod

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_modCode_selectedCarry
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
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
        isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV5 v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max v0 v1 v2 v3
            u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
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
  · have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; rw [← hbltu_0]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV5NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_max_from_source_exact_loopIterScratch_v5_noNop_modCode
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : ¬BitVec.ult u3 v2 := by rw [← hbltu_1]; decide
    have hb0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; exact hbltu_0.symm
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV5NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_max_call_from_source_exact_loopIterScratch_v5_noNop_modCode
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        ¬BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; rw [← hbltu_0]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          unfold loopN3UnifiedPostV5NoX1
          simp only at hp ⊢
          rw [sepConj_assoc'] at hp
          xperm_hyp hp)
        (divK_loop_n3_call_max_from_source_exact_loopIterScratch_v5_noNop_modCode
          sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
          retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)
  · have hb1 : BitVec.ult u3 v2 := hbltu_1.symm
    have hb0 :
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      simp only at hbltu_0; exact hbltu_0.symm
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        unfold loopN3UnifiedPostV5NoX1
        simp only at hp ⊢
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      (divK_loop_n3_call_call_from_source_exact_loopIterScratch_v5_noNop_modCode
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hb1 hcarry2_j1 hb0 hcarry2_j0)

end EvmAsm.Evm64
