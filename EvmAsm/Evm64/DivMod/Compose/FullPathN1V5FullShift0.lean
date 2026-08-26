/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullShift0

  Full v5 n=1 DIV code path, shift=0 case (base → nopOff), over `divCode_noNop_v5`:
  the shift=0 preloop+loop (`evm_div_n1_to_denorm_shift0_spec_v5_noNop`) composed
  with the shift=0 DIV epilogue (`evm_div_shift0_epilogue_spec_v5_noNop`) via the
  epilogue bridge (`loopN1UnifiedPostV5_shift0_to_epiloguePre`).  Shift=0 analog of
  `evm_div_n1_full_spec_v5_noNop`.  The quotient digits land in the output slots
  (`R0.1, R1.1, R2.1, R3.1` = the four shift=0 loop digits).  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5BridgeShift0
public import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5

@[expose] public section

namespace EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem evm_div_n1_full_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin ((((8 + 21 + 24 + 4) + 13) + 632) + 12) base (base + nopOff)
      (divCode_noNop_v5 base)
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
         (.x5 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
         (.x6 ↦ᵣ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
         (.x7 ↦ᵣ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
         (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1) **
         ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
         ((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
         ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
         ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
         ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1) **
         ((sp + 32) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
         ((sp + 40) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
         ((sp + 48) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
         ((sp + 56) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
        fullDivN1FrameShift0V5 sp base a0 a1 a2 a3 b0 scratchMem) := by
  have hA := evm_div_n1_to_denorm_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_z halign
  have hB := evm_div_shift0_epilogue_spec_v5_noNop sp base
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (clzResult b0).1
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (mulsubN4
        (div128Quot_v5 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
        b0 0 0 0 a0
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1).2.2.2.2
    (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1
    (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1
    (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1
    (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1
    b0 0 0 0 hshift_z
  have hBf := cpsTripleWithin_frameR
    (fullDivN1FrameShift0V5 sp base a0 a1 a2 a3 b0 scratchMem)
    (by rw [fullDivN1FrameShift0V5_unfold]; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hbr := loopN1UnifiedPostV5_shift0_to_epiloguePre sp base a0 a1 a2 a3 b0 scratchMem h hp
      xperm_hyp hbr) hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull



open EvmAsm.Rv64 in
/-- Shift=0 post bridge: the shift=0 full-path post implies the stack-dispatch
    DIV post (`divStackDispatchPostV5`), given the per-limb `div` facts. -/
theorem n1_shift0_post_to_divStackDispatchPost_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
         (.x5 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
         (.x6 ↦ᵣ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
         (.x7 ↦ᵣ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
         (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1) **
         ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
         ((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
         ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
         ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
         ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1) **
         ((sp + 32) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
         ((sp + 40) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
         ((sp + 48) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
         ((sp + 56) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
        fullDivN1FrameShift0V5 sp base a0 a1 a2 a3 b0 scratchMem) h →
      (divStackDispatchPost sp a b ** memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [fullDivN1FrameShift0V5_unfold] at hp
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := divStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (divStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _ hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
