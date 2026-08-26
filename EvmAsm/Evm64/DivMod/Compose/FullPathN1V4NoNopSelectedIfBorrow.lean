/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopSelectedIfBorrow

  No-NOP selected-if-borrow wrappers for the n=1 v4 call/max/max/max path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelectedIfBorrow
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMaxInput

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled first j=3 call-body step over `divCode_noNop_v4`, using the
    selected-if-borrow input hypothesis surface. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec
  exact divK_loop_n1_call_j3_exact_x1_framed_v4_noNop I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowCall I hh))

/-- Bundled all-max tail after the first j=3 call-body step over
    `divCode_noNop_v4`, using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_noNop_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpec
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)

/-- Bundled framed all-max tail pre/post over `divCode_noNop_v4`, using
    selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_noNop_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow
    I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over `divCode_noNop_v4`, using
    selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210FramedExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input_of_selected_if_borrow_input I hh)

/-- Full bundled N1 call/max/max/max exact path over `divCode_noNop_v4`,
    using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxExactInputSpec
  unfold loopN1CallMaxmaxmaxExactX1ScratchSpec
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input_of_selected_if_borrow
    I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input_of_selected_if_borrow_input
    I hh
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec at Htail
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max bundled
    inputs over `divCode_noNop_v4`, using the selected-if-borrow input
    hypothesis surface. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop_of_selected_if_borrow_input
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpec
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop_of_selected_if_borrow_input
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

/-- Full-DIV n=1 v4/no-NOP preloop composed with the call/max/max/max loop
    path, generalized over incoming `x9`, using selected-if-borrow input
    hypotheses. -/
theorem fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_noNop_x9In_of_selected_if_borrow_input
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hselected : fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1PreloopCallMaxmaxmaxExactSpecX9In sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecX9In
  have hPre := evm_div_n1_to_loopSetup_spec_v4_noNop_x9In_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
  have hLoop := fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop_of_selected_if_borrow_input
    sp base
    jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
    (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
    a0 a1 a2 a3 b0 b1 b2 b3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hselected
  unfold fullDivN1CallMaxmaxmaxExactInputSpec at hLoop
  unfold loopN1CallMaxmaxmaxExactInputSpec at hLoop
  unfold loopN1CallMaxmaxmaxExactX1ScratchSpec at hLoop
  unfold fullDivN1CallMaxmaxmaxExactInputs at hLoop
  dsimp only at hLoop
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hLoop
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      exact loopSetupPost_to_fullDivN1CallMaxmaxmaxScratchPreNoX1_framed
        sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
        jMem retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hPre hLoopF

/-- Full-DIV n=1 v4/no-NOP preloop, selected call/max/max/max loop path,
    and denormalization+DIV epilogue, generalized over incoming `x9`. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_noNop_x9In_of_selected_if_borrow_input
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hselected : fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
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
         (.x1 ↦ᵣ raVal))))
      (fullDivN1CallMaxmaxmaxUnifiedPostNoX1 sp base (clzResult b0).1
        a0 a1 a2 a3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (0 : Word) (0 : Word) (0 : Word)
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hA := fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_noNop_x9In_of_selected_if_borrow_input
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecX9In at hA
  have hB := evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_noNop_exact_x1
    sp base (clzResult b0).1
    a0 a1 a2 a3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    (0 : Word) (0 : Word) (0 : Word)
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    scratchMem raVal hshift_nz
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hpBridge := loopN1CallMaxmaxmaxScratchPostNoX1_to_denormPre_frame
        sp base
        a0 a1 a2 a3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (0 : Word) (0 : Word) (0 : Word)
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        scratchMem (clzResult b0).1 raVal h hp
      xperm_hyp hpBridge)
    hA hB

end EvmAsm.Evm64
