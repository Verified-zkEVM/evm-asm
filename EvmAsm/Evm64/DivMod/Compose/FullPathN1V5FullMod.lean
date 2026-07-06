/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullMod

  Full n=1 MOD code path over `modCode_noNop_v5` (shift ≠ 0): preloop + capped
  loop + MOD remainder denorm-epilogue, `base → nopOff`.  MOD mirror of
  `evm_div_n1_full_spec_v5_noNop` (FullPathN1V5Full): the entry→denorm path and the
  op-agnostic loop-post → denorm-pre bridge (`loopN1UnifiedPostV5_to_denormPreV5`)
  are shared; only the epilogue differs — MOD reads the un-normalized REMAINDER
  (`evm_mod_preamble_denorm_epilogue_spec_v5_noNop`, post `denormModPost`) where
  DIV reads the quotient.  The quotient output cells (sp+4088/4080/4072/4064),
  unused by the MOD epilogue, are framed through to the post.  Step 3 of the n=1
  MOD lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenormMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod

namespace EvmAsm.Evm64
open EvmAsm.Rv64 EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

/-- Full n=1 MOD code path over `modCode_noNop_v5` (shift ≠ 0): preloop + capped
    loop + MOD remainder epilogue, `base → nopOff`.  The un-normalized remainder
    limbs land in `denormModPost`; the quotient digits remain in the output cells
    (framed, unread). -/
theorem evm_mod_n1_full_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 632 + (2 + 23 + 10)) base (base + nopOff)
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
      ((denormModPost sp (fullDivN1Shift b0)
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 **
        ((sp + signExtend12 3992) ↦ₘ fullDivN1Shift b0)) **
       (((sp + signExtend12 4088) ↦ₘ
            (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1) **
         ((sp + signExtend12 4080) ↦ₘ
            (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1) **
         ((sp + signExtend12 4072) ↦ₘ
            (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1) **
         ((sp + signExtend12 4064) ↦ₘ
            (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1)) **
       fullDivN1FrameV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hshift_nz' : fullDivN1Shift b0 ≠ 0 := by simp only [fullDivN1Shift]; exact hshift_nz
  have hA := evm_mod_n1_to_denorm_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_nz halign
  have hB := evm_mod_preamble_denorm_epilogue_spec_v5_noNop sp base
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1Shift b0)
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    hshift_nz'
  have hBf := cpsTripleWithin_frameR
    (((sp + signExtend12 4088) ↦ₘ
        (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1) **
      ((sp + signExtend12 4080) ↦ₘ
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1) **
      ((sp + signExtend12 4072) ↦ₘ
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1) **
      ((sp + signExtend12 4064) ↦ₘ
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1) **
      fullDivN1FrameV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)
    (by delta fullDivN1FrameV5; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show ((clzResult b0).1) = fullDivN1Shift b0 from by simp only [fullDivN1Shift]] at hp
      have hbr := loopN1UnifiedPostV5_to_denormPreV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem h hp
      rw [fullDivN1DenormPreV5_unfold] at hbr
      simp only [se12_32, se12_40, se12_48, se12_56] at hbr
      xperm_hyp hbr)
    hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
