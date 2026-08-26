module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelected
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelectedIfBorrow

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full-code full-DIV n=1 preloop plus call/max/max/max path, generalized
    over the incoming `x9` value. -/
@[irreducible]
def fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) : Prop :=
  cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) base (base + denormOff)
    (divCode_v4 base)
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
    ((loopN1CallMaxmaxmaxScratchPostNoX1 sp base
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
      scratchMem ** (.x1 ↦ᵣ raVal)) **
     (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)))

/-- Full-DIV n=1 preloop with arbitrary incoming `x9`, composed with the
    call/max/max/max loop path over the full `divCode_v4` bundle. -/
theorem fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_bltu
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
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In
  have hPre := evm_div_n1_to_loopSetup_spec_v4_x9In_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
  have hLoop := fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_bltu
    sp base
    jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
    (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
    a0 a1 a2 a3 b0 b1 b2 b3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu3 hbltu2 hbltu1 hbltu0 hcarry2
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4 at hLoop
  unfold loopN1CallMaxmaxmaxExactInputSpecV4 at hLoop
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

/-- Full-DIV n=1 preloop with arbitrary incoming `x9`, composed with the
    call/max/max/max loop path over the full `divCode_v4` bundle using the
    selected-only loop hypothesis surface. -/
theorem fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_selected
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
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In
  have hPre := evm_div_n1_to_loopSetup_spec_v4_x9In_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
  have hLoop := fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_selected
    sp base
    jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
    (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
    a0 a1 a2 a3 b0 b1 b2 b3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hselected
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4 at hLoop
  unfold loopN1CallMaxmaxmaxExactInputSpecV4 at hLoop
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

/-- Full-DIV n=1 preloop with arbitrary incoming `x9`, composed with the
    call/max/max/max loop path over the full `divCode_v4` bundle using the
    selected-only loop hypothesis surface and conditional max carry evidence. -/
theorem fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_selected_if_borrow
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
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In
  have hPre := evm_div_n1_to_loopSetup_spec_v4_x9In_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
  have hLoop := fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_selected_if_borrow
    sp base
    jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
    (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
    a0 a1 a2 a3 b0 b1 b2 b3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hselected
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4 at hLoop
  unfold loopN1CallMaxmaxmaxExactInputSpecV4 at hLoop
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

/-- Full-DIV n=1 preloop with arbitrary incoming `x9`, composed with the
    call/max/max/max loop path over the full `divCode_v4` bundle using the
    selected-if-borrow loop hypothesis surface. -/
theorem fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_selected_if_borrow_input
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
    fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In
  have hPre := evm_div_n1_to_loopSetup_spec_v4_x9In_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
  have hLoop := fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_selected_if_borrow_input
    sp base
    jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
    (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
    a0 a1 a2 a3 b0 b1 b2 b3
    (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hselected
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4 at hLoop
  unfold loopN1CallMaxmaxmaxExactInputSpecV4 at hLoop
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

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, with caller `x1` retained exactly. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_of_bltu
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
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
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
         (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_noNop_of_bltu
      sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz halign hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, generalized over the incoming `x9` value,
    using the selected-only loop hypothesis surface. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected
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
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
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
  have hA := fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_selected
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In at hA
  have hB := evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_exact_x1
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

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, generalized over the incoming `x9` value,
    using selected-only hypotheses and conditional max carry evidence. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected_if_borrow
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
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
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
  have hA := fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_selected_if_borrow
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In at hA
  have hB := evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_exact_x1
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

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, generalized over the incoming `x9` value,
    using selected-if-borrow hypotheses. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected_if_borrow_input
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
      base (base + nopOff) (divCode_v4 base)
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
  have hA := fullDivN1_preloop_call_maxmaxmax_exact_x1_scratch_v4_x9In_of_selected_if_borrow_input
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected
  unfold fullDivN1PreloopCallMaxmaxmaxExactSpecV4X9In at hA
  have hB := evm_div_n1_call_maxmaxmax_denorm_epilogue_spec_v4_exact_x1
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

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, with caller `x1` retained exactly, using
    the selected-only loop hypothesis surface. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_of_selected
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
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
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
         (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
  exact fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, with caller `x1` retained exactly, using
    selected-only hypotheses and conditional max carry evidence. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_of_selected_if_borrow
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
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
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
         (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
  exact fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected_if_borrow
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, with caller `x1` retained exactly, using
    selected-if-borrow hypotheses. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_of_selected_if_borrow_input
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
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
      base (base + nopOff) (divCode_v4 base)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
         (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
  exact fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected_if_borrow_input
    sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign hselected

/-- Full-code full-DIV n=1 preloop, call/max/max/max loop path, and
    denormalization+DIV epilogue, generalized over the incoming `x9` value. -/
theorem fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_bltu
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
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
      base (base + nopOff) (divCode_v4 base)
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
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_noNop_x9In_of_bltu
      sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz halign hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

end EvmAsm.Evm64
