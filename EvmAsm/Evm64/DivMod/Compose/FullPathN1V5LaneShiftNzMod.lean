/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShiftNzMod

  The v5 n=1 MOD lane, shift≠0 case: from the stack-dispatch precondition to
  `modStackDispatchPostV5`, over `modCode_noNop_v5`.  MOD mirror of
  `evm_div_n1_lane_shiftNz_v5` (FullPathN1V5LaneShiftNz): composes the op-agnostic
  pre lift (`n1_dispatchPre_to_pathEntry_v5`), the full MOD code path
  (`evm_mod_n1_full_spec_v5_noNop`), and a MOD post bridge
  (`n1_denormModPost_to_modStackDispatchPost_v5`, with the remainder-limb facts
  from `fullModN1RemainderWordV5_eq_mod_lane_of_shape`).  Step 6 of the n=1 MOD lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullMod
import EvmAsm.Evm64.DivMod.Spec.N1V5ModRemainder
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

open EvmAsm.Rv64 in
/-- The v5 n=1 MOD full-path post (`denormModPost`-form + quotient cells + frame)
    implies the stack-dispatch MOD post, given the per-limb `mod` facts (supplied by
    the lane from the remainder theorem) and the dividend limbs.  MOD mirror of
    `n1_denormPost_to_divStackDispatchPost_v5`. -/
theorem n1_denormModPost_to_modStackDispatchPost_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN1Shift b0).toNat % 64))) :
    ∀ h,
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
       fullDivN1FrameV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) h →
      (modStackDispatchPost sp a b ** memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  delta denormModPost fullDivN1FrameV5 at hp
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := modStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (modStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ hmod0 hmod1 hmod2 hmod3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

/-- The v5 n=1 MOD lane, shift≠0: stack-dispatch precondition → `modStackDispatchPostV5`. -/
theorem evm_mod_n1_lane_shiftNz_v5 (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b0).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hmodWord := fullModN1RemainderWordV5_eq_mod_lane_of_shape
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb1z hb2z hb3z hshift_nz
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ := fullModN1V5_hmods_of_word_eq a b a0 a1 a2 a3 b0 b1 b2 b3 hmodWord
  have hpath := evm_mod_n1_full_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_nz halign
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n1_dispatchPre_to_pathEntry_v5 sp a b x1Val v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta modStackDispatchPostV5
    exact n1_denormModPost_to_modStackDispatchPost_v5 sp base a b a0 a1 a2 a3 b0 b1 b2 b3 scratchMem
      ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq

end EvmAsm.Evm64
