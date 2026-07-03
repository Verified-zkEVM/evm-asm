/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExactMod

  The n=1 v5 x1-preserving (callable exact-frame) MOD full path over
  `modCode_noNop_v5` (shift ≠ 0): the x1-preserving MOD entry→denorm rung + the
  MOD remainder denorm-epilogue, carrying the concrete return address `x1 = x1Val`
  and a free incoming `x9In`/`x2In`.  MOD mirror of the DIV
  `evm_div_n1_{to_denorm,full}_spec_v5_noNop_preserving_x1`
  (`FullPathN1V5CallableExact`): the preloop leaf + capped loop + loop-post→denorm
  bridge + `fullDivN1FrameV5NoX1` frame are op-agnostic (shared), so they are
  reused verbatim; only the code surface (`divCode_noNop_v5` → `modCode_noNop_v5`),
  the preloop leaf (`evm_mod_n1_to_loopSetup_spec_within_v5_noNop`), the code
  extension (`sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5`), and the epilogue
  (`evm_mod_preamble_denorm_epilogue_spec_v5_noNop`, post `denormModPost`) differ.
  Step toward `evm_mod_callable_v5` correctness (SMOD `.proven` track).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenormMod
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExact
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullMod

namespace EvmAsm.Evm64
open EvmAsm.Rv64 EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

/-- x1-preserving twin of `evm_mod_n1_to_denorm_spec_v5_noNop`: entry→denorm over
    `modCode_noNop_v5` with the concrete `x1Val` framed through the preloop and the
    x1-free loop, and a free incoming `x9In`/`x2In`.  Op-agnostic through denorm, so
    the loop post is the shared `loopN1UnifiedPostV5NoX1`. -/
theorem evm_mod_n1_to_denorm_spec_v5_noNop_preserving_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 632) base (base + denormOff)
      (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
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
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
      ((loopN1UnifiedPostV5NoX1 sp base
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 scratchMem) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) ** (.x1 ↦ᵣ x1Val)) := by
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0 := a0 <<< (shift.toNat % 64)
  -- 1. Preloop: base → base + loopBodyOff (x1 framed concrete), MOD code
  have hPre := evm_mod_n1_to_loopSetup_spec_within_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In x2In
    hbnz hb3z hb2z hb1z hshift_nz
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) **
     ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) **
     ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) hPre
  -- 2. x1-preserving loop at normalized shape (extend shared → mod code)
  have hLoop0 := divK_loop_n1_call_unified_v5_of_shape_preserving_x1 sp jMem (1 : Word) shift u0
    (a0 >>> (antiShift.toNat % 64)) v11Old antiShift
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) x1Val retMem dMem dloMem scratch_un0 scratchMem base halign
    a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hLoop := cpsTripleWithin_extend_code sharedDivModCodeNoNop_v5_sub_modCode_noNop_v5 hLoop0
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopSetupPost at hp
      simp only [x1_val_n1] at hp
      unfold loopN1UnifiedPreV5NoX1 loopN1PreWithScratchNoX1 loopN1Pre
      unfold fullDivN1NormV fullDivN1NormU fullDivN1AntiShift fullDivN1Shift
      simp only [n1_ub3_off0, n1_ub3_off4088, n1_ub3_off4080,
                  n1_ub3_off4072, n1_ub3_off4064,
                  n2_ub2_off0,
                  n3_ub1_off0,
                  n3_ub0_off0,
                  n1_qa3, n2_qa2, n3_qa1, n3_qa0,
                  se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- x1-preserving twin of `evm_mod_n1_full_spec_v5_noNop`: full n=1 MOD path
    `base → nopOff` with the concrete `x1Val` framed and the x1-free frame; the
    remainder limbs land in `denormModPost`, the quotient digits framed unread. -/
theorem evm_mod_n1_full_spec_v5_noNop_preserving_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val x9In x2In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 632 + (2 + 23 + 10)) base (base + nopOff)
      (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
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
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
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
       fullDivN1FrameV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  have hshift_nz' : fullDivN1Shift b0 ≠ 0 := by simp only [fullDivN1Shift]; exact hshift_nz
  have hA := evm_mod_n1_to_denorm_spec_v5_noNop_preserving_x1 sp base a0 a1 a2 a3 b0 b1 b2 b3
    v5 v6 v7 v10 v11Old x1Val x9In x2In
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
      fullDivN1FrameV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
      (.x1 ↦ᵣ x1Val))
    (by delta fullDivN1FrameV5NoX1; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show ((clzResult b0).1) = fullDivN1Shift b0 from by simp only [fullDivN1Shift]] at hp
      have hbr := loopN1UnifiedPostV5NoX1_to_denormPreV5 sp base a0 a1 a2 a3 b0 b1 b2 b3
        scratchMem x1Val h hp
      rw [fullDivN1DenormPreV5_unfold] at hbr
      simp only [se12_32, se12_40, se12_48, se12_56] at hbr
      xperm_hyp hbr)
    hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
