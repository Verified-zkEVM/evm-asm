/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneShiftNz

  The v5 n=2 DIV lane, shift≠0 case: from the stack-dispatch precondition to
  `divStackDispatchPostV5`, over `divCode_noNop_v5`.  Composes the entry→nopOff
  path with the carry discharged from shape
  (`evm_div_n2_stack_pre_to_unified_post_v5_noNop_fromShape`, #7463), the post
  bridge (`fullDivN2UnifiedPostNoX1V5_to_divStackDispatchPostV5`, #7464) with the
  shape-derived quotient correctness
  (`fullDivN2QuotientWordV5_eq_div_lane_of_shape`), and the step-count widening to
  `unifiedDivBound`.  This is the shift≠0 half of `lane_n2` matching
  `evm_div_stack_spec_unconditional_of_lanes_v5_div`, mirroring
  `evm_div_n1_lane_shiftNz_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFromShape
import EvmAsm.Evm64.DivMod.Spec.N2V5PostToDispatchPostV5
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientLaneShape
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem evm_div_n2_lane_shiftNz_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  -- The three runtime borrow flags, in clean `ult (fullDivN2R{2,1}V5 …)` form.
  obtain ⟨bltu_2, hbltu_2⟩ :
      ∃ x, x = BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 := ⟨_, rfl⟩
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 := ⟨_, rfl⟩
  -- The per-digit `bltu` path matches, from the clean flag definitions.
  have hc2 : bltu_2 = true →
      BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 = true := fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false →
      ¬ BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 := fun h => by rw [← hbltu_2, h]; decide
  have hc1 : bltu_1 = true →
      BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 = true := fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 := fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 = true := fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1 := fun h => by rw [← hbltu_0, h]; decide
  -- Quotient correctness from shape (lane form).
  have hdivWord := fullDivN2QuotientWordV5_eq_div_lane_of_shape bltu_2 bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  -- The entry→nopOff path with carry discharged from shape.
  have hpath := evm_div_n2_stack_pre_to_unified_post_v5_noNop_fromShape sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal (signExtend12 (4 : BitVec 12) - (4 : Word))
    ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
    bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2 hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken (fun _ hp => hp) ?_ hpath
  intro h hq
  exact fullDivN2UnifiedPostNoX1V5_to_divStackDispatchPostV5 bltu_2 bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratch_un0 scratchMem raVal hdivWord h hq

end EvmAsm.Evm64
