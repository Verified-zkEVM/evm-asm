/- Shared declaration home for the MOD n=2 V5 lane and shape path. -/

import EvmAsm.Evm64.DivMod.Spec.N2V5ModPostShared
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientLaneShapeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallablePostSelectedBorrowCarryMod
import EvmAsm.Evm64.DivMod.Spec.N2V5BundleOfShape
import EvmAsm.Evm64.DivMod.Spec.N2V5R2R1Dispatch

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem evm_mod_n2_stack_pre_to_unified_post_v5_noNop_fromShape (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal x9In x2In : Word)
    (bltu_2 bltu_1 bltu_0 : Bool)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 =
      BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_0 : bltu_0 =
      BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 702) + (2 + 23 + 10))
      base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  apply evm_mod_n2_stack_pre_to_unified_post_v5_noNop_borrowCarry sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2
  case hbltu_1 =>
    -- match form, from clean form via dispatch-eq (full simp reduces the
    -- proof-discriminated match)
    cases bltu_2 <;> simpa [fullDivN2R2V5_eq_dispatch] using hbltu_1
  case hbltu_0 =>
    cases bltu_2 <;> cases bltu_1 <;>
      simpa [fullDivN2R1V5_eq_dispatch, fullDivN2R2V5_eq_dispatch] using hbltu_0
  case hcarry =>
    -- discharge from shape (#7461); flags trivial from clean form
    apply loopN2SelectedBorrowCarryV5_of_shape
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz
    · intro h; rw [← hbltu_2]; exact h
    · intro h; rw [← hbltu_2, h]; decide
    · intro h; rw [← hbltu_1]; exact h
    · intro h; rw [← hbltu_1, h]; decide
    · intro h; rw [← hbltu_0]; exact h
    · intro h; rw [← hbltu_0, h]; decide


open EvmAsm.Rv64

theorem evm_mod_n2_lane_shiftNz_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
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
  have hdivWord := fullModN2RemainderWordV5_eq_mod_lane_of_shape bltu_2 bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  -- The entry→nopOff path with carry discharged from shape.
  have hpath := evm_mod_n2_stack_pre_to_unified_post_v5_noNop_fromShape sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal
    (signExtend12 (4 : BitVec 12) - (4 : Word)) ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
    bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2 hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken (fun _ hp => hp) ?_ hpath
  intro h hq
  exact fullModN2UnifiedPostNoX1V5_to_modStackDispatchPostV5 bltu_2 bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratch_un0 scratchMem raVal hdivWord h hq


open EvmAsm.Rv64

/-- n=2 lane = shift=0 lane ⊕ shift≠0 lane (#7465), combined by `by_cases` on the
    normalization shift. -/
theorem evm_mod_n2_lane_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (shift0lane : (clzResult (b.getLimbN 1)).1 = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostV5 sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 1)).1 = 0
  · exact shift0lane hsh
  · exact evm_mod_n2_lane_shiftNz_v5 sp base a b raVal v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1nz hsh halign

end EvmAsm.Evm64
