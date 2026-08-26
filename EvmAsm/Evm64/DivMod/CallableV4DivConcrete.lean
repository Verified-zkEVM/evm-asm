module

public import EvmAsm.Evm64.DivMod.CallableV4Div

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Path-bundled N2 DIV v4 callable wrapper preserving the concrete v4
    trial-call scratch value. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_path_word
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  have hbltu_2 := fullDivN2PathConditionsWordV4_trial_j2
    bltu_2 bltu_1 bltu_0 a b hpath
  have hbltu_1 := fullDivN2PathConditionsWordV4_trial_j1
    bltu_2 bltu_1 bltu_0 a b hpath
  have hbltu_0 := fullDivN2PathConditionsWordV4_trial_j0
    bltu_2 bltu_1 bltu_0 a b hpath
  have hcarry2 := fullDivN2PathConditionsWordV4_carry2
    bltu_2 bltu_1 bltu_0 a b hpath
  have hBody :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun h hq =>
        fullDivN2UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
          bltu_2 bltu_1 bltu_0 sp base a b
          retMem dMem dloMem scratchUn0 scratchMem raVal
          (fullDivN2QuotientWordV4_eq_div_of_word_path_conditions_ne_zero
            bltu_2 bltu_1 bltu_0 a b hbnz hpath)
          h hq)
      (evm_div_n2_stack_pre_to_unified_post_v4_noNop sp base a b
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
        hbnz hb3z hb2z hb1nz hshift_nz halign
        (by simpa [isTrialN2V4_j2] using hbltu_2)
        (by
          cases bltu_2 <;>
            simpa [isTrialN2V4_j1, fullDivN2R2V4, iterN2V4] using hbltu_1)
        (by
          cases bltu_2 <;> cases bltu_1 <;>
            simpa [isTrialN2V4_j0, fullDivN2R1V4, fullDivN2R2V4, iterN2V4] using hbltu_0)
        hcarry2)
  have hBodyUnified :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal
          (signExtend12 4095 : Word) **
         ((sp + signExtend12 3936) ↦ₘ
          fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            scratchMem)) :=
    cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) hBody
  exact
    evm_div_callable_v4_spec_from_divCode_noNop_exact_frame_x9out_body_frame_transform
      (FPre := ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (FPost := ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem))
      sp base (signExtend12 (4 : BitVec 12) - (4 : Word))
      (signExtend12 4095 : Word) raVal a b
      ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hBodyUnified

/-- Path-bundled N2 DIV v4 callable wrapper preserving the concrete v4
    trial-call scratch value, with dispatcher-style limb-or nonzero input. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_path_limbNz
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_path_word
    bltu_2 bltu_1 bltu_0 sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    ((EvmWord.ne_zero_iff_getLimbN_or).mpr hbnz)
    hb3z hb2z hb1nz hshift_nz halign hpath

/-- Path-bundled N2 DIV v4 callable wrapper preserving the concrete v4
    trial-call scratch value, deriving divisor nonzero from the n=2 shape. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_path_shape
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) := by
  exact evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_path_limbNz
    bltu_2 bltu_1 bltu_0 sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    (n2_limb_or_ne_zero_of_limb1_ne_zero hb1nz) hb3z hb2z hb1nz
    hshift_nz halign hpath

end EvmAsm.Evm64
