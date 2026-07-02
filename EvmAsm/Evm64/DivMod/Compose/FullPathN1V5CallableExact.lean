/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5CallableExact

  The n=1 v5 x1-preserving (callable exact-frame) full path over
  `divCode_noNop_v5` (shift ≠ 0): preloop + x1-preserving capped loop
  (LoopIterN1/NoX1ChainV5) + denorm epilogue, landing the callable exact-frame
  dispatch post `divStackDispatchPostCallableExactFrame` (concrete `x1 = raVal`,
  `x9 = -1`).  Mirror of the bundled `FullPathN1V5ToDenorm`/`FullPathN1V5Full`
  chain with `regOwn .x1` replaced by the framed concrete return address, and of
  the n=2 exact lane (`N2V5CallableExact`) one divisor size down.  Step toward
  `evm_div_callable_v5` correctness (SDIV `.proven` track).
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.NoX1ChainV5
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64
open EvmAsm.Rv64 EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

/-- `fullDivN1FrameV5` minus the trailing `regOwn .x1` (the concrete return
    address is framed outside instead). -/
@[irreducible] def fullDivN1FrameV5NoX1 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let R3 := fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3
  let R2 := fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3
  let R1 := fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3
  let R0 := fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ v.1) **
  ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo v.1) **
  ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 u.1) **
  ((sp + signExtend12 3936) ↦ₘ
    divKTrialCallV5ScratchOut R1.2.1 u.1 v.1
      (divKTrialCallV5ScratchOut R2.2.1 u.2.1 v.1
        (divKTrialCallV5ScratchOut R3.2.1 u.2.2.1 v.1
          (divKTrialCallV5ScratchOut u.2.2.2.2 u.2.2.2.1 v.1 scratchMem))))

attribute [local irreducible] EvmWord.val256 div128Quot_v5 iterWithDoubleAddback mulsubN4 clzResult

private theorem iterN1Call_v5_unfoldU'' (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5; rfl

/-- x1-free twin of `loopN1UnifiedPostV5_to_denormPreV5`: the x1-free loop
    result at `denormOff` reduces to the denorm-epilogue pre plus the x1-free
    frame. -/
theorem loopN1UnifiedPostV5NoX1_to_denormPreV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem raVal : Word)
    (h : PartialState)
    (hp : (loopN1UnifiedPostV5NoX1 sp base
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 scratchMem **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ fullDivN1Shift b0) ** (.x1 ↦ᵣ raVal)) h) :
    (fullDivN1DenormPreV5 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN1FrameV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
     (.x1 ↦ᵣ raVal)) h := by
  delta fullDivN1DenormPreV5 fullDivN1C3V5 fullDivN1FrameV5NoX1
  rw [← fullN1S0_eq_fullDivN1R0V5, ← fullN1S1_eq_fullDivN1R1V5, ← fullN1S2_eq_fullDivN1R2V5,
      fullDivN1R3V5_eq_iterN1Call_v5]
  delta loopN1UnifiedPostV5NoX1 loopN1Iter210PostV5NoX1 loopN1Iter10PostV5NoX1 loopIterPostN1V5NoX1
    loopIterPostN1CallV5NoX1 at hp
  dsimp only [] at hp
  rw [loopExitPostN1_j0_eq] at hp
  rw [← iterN1Call_v5_unfoldU''] at hp
  simp only [n1_ub3_off4064, n1_qa3, n2_ub2_off4064, n2_qa2,
      n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56,
      sepConj_emp_right'] at hp ⊢
  delta fullN1S0 fullN1S1 fullN1S2 at *
  dsimp only [] at hp ⊢
  simp only [iterN1V5_true, if_true] at hp ⊢
  set R3 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
    with hR3
  set R2 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 R3.2.1 R3.2.2.1 R3.2.2.2.1 R3.2.2.2.2.1
    with hR2
  set R1 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1 R2.2.1 R2.2.2.1 R2.2.2.2.1 R2.2.2.2.2.1
    with hR1
  set R0 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).1 R1.2.1 R1.2.2.1 R1.2.2.2.1 R1.2.2.2.2.1
    with hR0
  xperm_chunked hp

/-- x1-preserving twin of `evm_div_n1_to_denorm_spec_v5_noNop`: entry→denorm
    with the concrete `x1Val` framed through the preloop and the x1-free loop. -/
theorem evm_div_n1_to_denorm_spec_v5_noNop_preserving_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 632) base (base + denormOff)
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
  -- 1. Preloop: base → base + loopBodyOff (x1 framed concrete)
  have hPre := evm_div_n1_to_loopSetup_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3z hb2z hb1z hshift_nz
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     ((sp + signExtend12 3968) ↦ₘ retMem) **
     ((sp + signExtend12 3960) ↦ₘ dMem) **
     ((sp + signExtend12 3952) ↦ₘ dloMem) **
     ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
    (by pcFree) hPre
  -- 2. x1-preserving loop at normalized shape (extend shared → div code)
  have hLoop0 := divK_loop_n1_call_unified_v5_of_shape_preserving_x1 sp jMem (1 : Word) shift u0
    (a0 >>> (antiShift.toNat % 64)) v11Old antiShift
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) x1Val retMem dMem dloMem scratch_un0 scratchMem base halign
    a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hLoop := cpsTripleWithin_extend_code sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5 hLoop0
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

/-- x1-preserving twin of `evm_div_n1_full_spec_v5_noNop`: full n=1 path
    `base → nopOff` with the concrete `x1Val` framed and the x1-free frame. -/
theorem evm_div_n1_full_spec_v5_noNop_preserving_x1 (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x1Val : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 632 + (2 + 23 + 10)) base (base + nopOff)
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
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val))
      ((denormDivPost sp (fullDivN1Shift b0)
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 **
        ((sp + signExtend12 3992) ↦ₘ fullDivN1Shift b0)) **
       fullDivN1FrameV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ x1Val)) := by
  have hshift_nz' : fullDivN1Shift b0 ≠ 0 := by simp only [fullDivN1Shift]; exact hshift_nz
  have hA := evm_div_n1_to_denorm_spec_v5_noNop_preserving_x1 sp base a0 a1 a2 a3 b0 b1 b2 b3
    v5 v6 v7 v10 v11Old x1Val
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_nz halign
  have hB := evm_div_preamble_denorm_epilogue_spec_v5_noNop sp base
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1Shift b0)
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    hshift_nz'
  have hBf := cpsTripleWithin_frameR
    (fullDivN1FrameV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
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

open EvmAsm.Rv64 in
/-- x1-preserving twin of `n1_dispatchPre_to_pathEntry_v5`: the dispatch pre
    keeps the concrete `x1Val` instead of weakening it to `regOwn .x1`. -/
theorem n1_dispatchPre_to_pathEntry_v5_preserving_x1 (sp : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3) :
    ∀ h,
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b0).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) h →
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
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val)) h := by
  intro h hp
  delta divModStackDispatchPreNoX1 at hp
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp b b0 b1 b2 b3 hb0 hb1 hb2 hb3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
  rw [word_add_zero]
  xperm_hyp hp

open EvmAsm.Rv64 in
/-- The x1-preserving n=1 v5 full-path post implies the callable exact-frame
    dispatch post (concrete `x1 = raVal`, `x9 = -1`), given the per-limb `div`
    facts.  Callable-exact twin of `n1_denormPost_to_divStackDispatchPost_v5`. -/
theorem n1_denormPostNoX1_to_divStackDispatchPostCallableExactFrame_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1) :
    ∀ h,
      ((denormDivPost sp (fullDivN1Shift b0)
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 **
        ((sp + signExtend12 3992) ↦ₘ fullDivN1Shift b0)) **
       fullDivN1FrameV5NoX1 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem **
       (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  delta denormDivPost fullDivN1FrameV5NoX1 at hp
  rw [word_add_zero] at hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  apply sepConj_mono_right
    (P := (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
      (.x9 ↦ᵣ (signExtend12 4095 : Word)))
    memIs_implies_memOwn h
  apply sepConj_mono_left (divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b) h
  rw [divConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _ hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hp

open EvmAsm.Rv64 in
/-- Unified-bound n=1 DIV v5 callable exact-frame lane (shift ≠ 0): the full
    x1-preserving path `base → nopOff` over `divCode_noNop_v5` from the callable
    dispatch pre to `divStackDispatchPostCallableExactFrame` (concrete
    `x1 = raVal`, `x9 = -1`).  n=1 mirror of
    `evm_div_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_uni`; the
    per-limb quotient facts are hypotheses (shape-level dischargers come with
    the lane assembly). -/
theorem evm_div_n1_stack_spec_noNop_v5_preNoX1_callableExactFrame_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old raVal : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = (fullDivN1R0V5 true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = (fullDivN1R1V5 true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (fullDivN1R2V5 true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (fullDivN1R3V5 true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  have hbody := evm_div_n1_full_spec_v5_noNop_preserving_x1 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old raVal
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem
    hbnz hb3z hb2z hb1z hshift_nz halign
  exact cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) <|
    cpsTripleWithin_weaken
      (fun h hp => n1_dispatchPre_to_pathEntry_v5_preserving_x1 sp a b
        raVal v5 v6 v7 v10 v11Old
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
        rfl rfl rfl rfl rfl rfl rfl rfl h hp)
      (fun h hq => n1_denormPostNoX1_to_divStackDispatchPostCallableExactFrame_v5
        sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem raVal rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3 h hq)
      hbody

end EvmAsm.Evm64
