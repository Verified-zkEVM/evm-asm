/-
  EvmAsm.Evm64.DivMod.Spec.N2V4CallableExact

  Unified-bound n=2 DIV v4 exact-frame callable wrapper over `divCode_noNop_v4`.

  `evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_uni` mirrors
  `evm_div_n3_stack_spec_noNop_v4_preNoX1_callableExactFrame_uni` (N3V4CallableExact)
  for the n=2 divisor case.

  The theorem takes the unified-post body proof as a hypothesis (rather than
  inlining the complex `hbltu_0` condition, which spans ~250 lines).  Callers
  first invoke `evm_div_n2_stack_pre_to_unified_post_v4_noNop` to obtain the
  body, then pass it here.

  The v4 trial-call scratch cell at `sp + signExtend12 3936` is existentially
  closed in the postcondition (`memOwn`), since its computed value is not needed
  by the dispatcher consumer.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2V4ConcretePostBridge
public import EvmAsm.Evm64.DivMod.Spec.N2QuotientStackBridge
public import EvmAsm.Evm64.DivMod.Spec.N2TrialWitnesses
public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopCallablePost
public import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified-bound n=2 DIV v4 body spec over `divCode_noNop_v4` with exact
    caller-framed `x1` and `x9` in the postcondition.  The v4 trial-call
    scratch cell at `sp + signExtend12 3936` is existentially closed (`memOwn`).

    `hbody` should be produced by `evm_div_n2_stack_pre_to_unified_post_v4_noNop`.
    This wrapper applies the bridge to convert the unified post to the callable
    exact frame, weakens the scratch cell, and lifts to `unifiedDivBound`. -/
theorem evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b)
    (hbody : cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 672) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal))) :
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
       memOwn (sp + signExtend12 3936)) :=
  cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        obtain ⟨h1, h2, hd, hu, hframe, hscratch⟩ := hq
        exact ⟨h1, h2, hd, hu, hframe, memIs_implies_memOwn h2 hscratch⟩)
      (cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hq =>
          fullDivN2UnifiedPostNoX1V4_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
            bltu_2 bltu_1 bltu_0 sp base a b
            retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hq)
        hbody)

/-- Selected-path N2 DIV v4 callable wrapper with the body proof supplied
    separately.

    This is the selected-carry analogue of
    `evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_uni` at the
    callable bridge layer: quotient correctness comes from the selected path
    package, while the body triple is left as an explicit input for the later
    selected-body retrofit. -/
theorem evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_selectedPathBody_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b)
    (hbody : cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 672) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal))) :
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
       memOwn (sp + signExtend12 3936)) := by
  exact evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_uni
    bltu_2 bltu_1 bltu_0 sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    (fullDivN2QuotientWordV4_eq_div_of_selected_word_path_conditions_ne_zero
      bltu_2 bltu_1 bltu_0 a b hbnz hpath) hbody

/-- Full-code form of
    `evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_selectedPathBody_uni`. -/
theorem evm_div_n2_stack_spec_v4_preNoX1_callableExactFrame_selectedPathBody_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b)
    (hbody : cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 672) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4 <|
    evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_selectedPathBody_uni
      bltu_2 bltu_1 bltu_0 sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hpath hbody

/-- No-NOP N2 callable wrapper with mechanical trial witnesses and a
    selected-path body factory. -/
theorem evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_autoTrialSelectedBody_uni
    (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hcarry : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hbody : ∀ bltu_2 bltu_1 bltu_0,
      fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b →
      cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 672) + (2 + 23 + 10))
        base (base + nopOff) (divCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem **
         (.x1 ↦ᵣ raVal))) :
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
       memOwn (sp + signExtend12 3936)) := by
  obtain ⟨bltu_2, bltu_1, bltu_0, hpath⟩ :=
    N2V4TrialWitnesses.exists_selected_path_conditions
      (n2V4TrialWitnesses_of_getLimbN a b) hcarry harith
  exact evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_selectedPathBody_uni
    bltu_2 bltu_1 bltu_0 sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hpath (hbody bltu_2 bltu_1 bltu_0 hpath)

/-- Full-code N2 callable wrapper with mechanical trial witnesses and a
    selected-path body factory.

    This hides the N2 branch booleans at the callable layer without requiring
    the false universal `fullDivN2Carry2NzV4` package.  The remaining lower
    body obligation is the selected-path triple supplied by `hbody`. -/
theorem evm_div_n2_stack_spec_v4_preNoX1_callableExactFrame_autoTrialSelectedBody_uni
    (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hcarry : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hbody : ∀ bltu_2 bltu_1 bltu_0,
      fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b →
      cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 672) + (2 + 23 + 10))
        base (base + nopOff) (divCode_noNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem **
         (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4 <|
    evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_autoTrialSelectedBody_uni
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hcarry harith hbody

/-- Legacy path-bundled N2 DIV v4 callable wrapper.

    This consumes the bundled raw-carry v4 path predicate, derives the branch/carry
    obligations for the body proof and the quotient-word equality for the
    callable exact-frame bridge, then closes the trial-call scratch cell as
    `memOwn`. -/
theorem evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_path_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
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
       memOwn (sp + signExtend12 3936)) := by
  have hbltu_2 := fullDivN2PathConditionsWordV4_trial_j2
    bltu_2 bltu_1 bltu_0 a b hpath
  have hbltu_1 := fullDivN2PathConditionsWordV4_trial_j1
    bltu_2 bltu_1 bltu_0 a b hpath
  have hbltu_0 := fullDivN2PathConditionsWordV4_trial_j0
    bltu_2 bltu_1 bltu_0 a b hpath
  have hcarry2 := fullDivN2PathConditionsWordV4_carry2
    bltu_2 bltu_1 bltu_0 a b hpath
  have hbody :=
    evm_div_n2_stack_pre_to_unified_post_v4_noNop sp base a b
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
      hcarry2
  exact evm_div_n2_stack_spec_noNop_v4_preNoX1_callableExactFrame_uni
    bltu_2 bltu_1 bltu_0 sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    (fullDivN2QuotientWordV4_eq_div_of_word_path_conditions_ne_zero
      bltu_2 bltu_1 bltu_0 a b hbnz hpath) hbody

end EvmAsm.Evm64
