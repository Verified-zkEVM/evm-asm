/-
  EvmAsm.Evm64.DivMod.Spec.N1ExactV4IfBorrowPathWord

  Small path-evidence wrappers over the selected-if-borrow N1 exact v4 stack
  surface.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1ExactV4IfBorrow
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopSelectedIfBorrow

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Full-v4 N1 stack wrapper consuming all-true N1 path evidence plus the
    selected quotient-word equality, avoiding the heavier semantic-facts
    package at this layer. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_if_borrow_path_word_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hdivWord : fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  exact
    evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_if_borrow_word
      sp base a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
      raVal
      rfl rfl rfl rfl rfl rfl rfl rfl
      hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu3 hbltu2 hbltu1 hbltu0
      (N1AllTruePathEvidence.selectedCarryIfBorrowFacts hpath)
      hdivWord

/-- Standard `preNoX1` form of
    `evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_if_borrow_path_word_getLimbN`.

    This keeps the selected-if-borrow path evidence and quotient-word equality
    surface while fixing the dispatcher scratch argument to the canonical no-x1
    value. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_path_word_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hdivWord : fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  exact
    evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_if_borrow_path_word_getLimbN
      sp base a b
      v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
      raVal
      hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hdivWord

/-- Standard `preNoX1` N1 selected-if-borrow path-word wrapper using the
    public EVM-word nonzero hypothesis. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_path_word_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hdivWord : fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  exact
    evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_path_word_getLimbN
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
      raVal
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
      hb3z hb2z hb1z hshift_nz halign
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hdivWord

/-- Standard `preNoX1` N1 selected-if-borrow path wrapper using semantic
    facts instead of exposing the quotient-word equality directly. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_path_semantic_facts_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  exact
    evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_of_selected_if_borrow_path_word_ne_zero_getLimbN
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
      raVal
      hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu3 hbltu2 hbltu1 hbltu0 hpath
      (fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_semantic_facts_word
        a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        rfl rfl rfl rfl rfl rfl rfl rfl
        ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
        hfacts)

/-- No-NOP variant of the N1 selected-if-borrow `input_hdivs` wrapper. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_noNop_of_selected_if_borrow_input_hdivs
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
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
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hdivs : FullDivN1CallMaxmaxmaxHdivs a b a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := hdivs
  have hFull :=
    fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_noNop_x9In_of_selected_if_borrow_input
      sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz halign hselected
  have hBody :
      cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
        base (base + nopOff) (divCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal
          ((clzResult b0).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
         ((sp + signExtend12 3936) ↦ₘ
          divKTrialCallV4ScratchOut
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
            (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) :=
    cpsTripleWithin_weaken
      (fun h hp => by
        rw [divModStackDispatchPreNoX1_unfold] at hp
        rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
            evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
            divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
        rw [word_add_zero]
        xperm_hyp hp)
      (fun h hp => by
        have hConcrete :=
          fullDivN1CallMaxmaxmaxUnifiedPostNoX1_to_divConcretePostNoX1Frame_extra
            sp base (clzResult b0).1 a b
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
            scratchMem raVal
            ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp
        refine sepConj_mono_left (fun hLeft hpLeft => ?_) h hConcrete
        simpa [divStackDispatchPostCallableExactFrame_unfold] using
          divConcretePostNoX1_weaken_callable_frame sp a b hLeft hpLeft)
      hFull
  exact cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) hBody

/-- No-NOP N1 selected-if-borrow stack wrapper consuming all-true path evidence
    plus semantic facts for the canonical `getLimbN` inputs.

    This is the `divCode_noNop_v4` surface required by the callable v4 frame
    transform. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExactFrame_unified_noNop_of_selected_if_borrow_path_semantic_facts_ne_zero_getLimbN
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
          (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
          (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1 scratchMem)) := by
  have hevidence :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_path_evidence_getLimbN
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts
  have hselected :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
      sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  have hdivs :=
    FullDivN1CallMaxmaxmaxHdivs_of_path_evidence_getLimbN
      sp base a b
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_noNop_of_selected_if_borrow_input_hdivs
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old (signExtend12 (4 : BitVec 12) - (4 : Word))
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl
    ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hb3z hb2z hb1z
    hshift_nz halign hselected hdivs

end EvmAsm.Evm64
