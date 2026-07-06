/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShift0Mod

  The v5 n=1 MOD lane, shift=0 case + the full `evm_mod_n1_lane_v5` combiner.
  MOD mirror of `FullPathN1V5LaneShift0` (DIV).  Composes the op-agnostic pre lift
  (`n1_dispatchPre_to_pathEntry_v5`), the full shift=0 MOD code path
  (`evm_mod_n1_full_shift0_spec_v5_noNop`), and a shift=0 MOD post bridge
  (with the remainder-limb facts from `fullModN1RemainderWordShift0V5_eq_mod_lane_of_shape`).
  The combiner case-splits `(clzResult b0).1 = 0` to unify the shift0 and shift≠0
  halves into one lane theorem over `modCode_noNop_v5` → `modStackDispatchPostV5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FullShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShiftNzMod
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0ModRemainder

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Project the shift=0 MOD remainder-word equality into the four per-limb
    `getLimbN` facts (the values in the output cells sp+32/40/48/56). -/
theorem fullModN1Shift0V5_hmods_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 : Word)
    (hword : fullModN1RemainderWordShift0V5 a0 a1 a2 a3 b0 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1 ∧
    (EvmWord.mod a b).getLimbN 1 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hword]; delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hword]; delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hword]; delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hword]; delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_3

open EvmAsm.Rv64 in
/-- Shift=0 MOD post bridge: the shift=0 full-path post implies the stack-dispatch
    MOD post (`modStackDispatchPostV5`), given the per-limb `mod` facts.  MOD mirror
    of `n1_shift0_post_to_divStackDispatchPost_v5`. -/
theorem n1_shift0_modPost_to_modStackDispatchPost_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1)
    (hmod1 : (EvmWord.mod a b).getLimbN 1 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1)
    (hmod2 : (EvmWord.mod a b).getLimbN 2 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1)
    (hmod3 : (EvmWord.mod a b).getLimbN 3 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
         (.x5 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         (.x6 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         (.x7 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
         ((sp + signExtend12 4056) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         ((sp + signExtend12 4048) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         ((sp + signExtend12 4040) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         ((sp + signExtend12 4032) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
         ((sp + 32) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1) **
         ((sp + 40) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1) **
         ((sp + 48) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1) **
         ((sp + 56) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1)) **
        (((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
          ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
          ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
          ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)) **
        fullModN1FrameShift0V5Rest sp base a0 a1 a2 a3 b0 scratchMem) h →
      (modStackDispatchPost sp a b ** memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [fullModN1FrameShift0V5Rest_unfold] at hp
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := modStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (modStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ hmod0 hmod1 hmod2 hmod3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

/-- The v5 n=1 MOD lane, shift=0: stack-dispatch precondition → `modStackDispatchPostV5`. -/
theorem evm_mod_n1_lane_shift0_v5 (sp base : Word) (a b : EvmWord)
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
    (hshift_z : (clzResult b0).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b0).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hmodWord := fullModN1RemainderWordShift0V5_eq_mod_lane_of_shape
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb1z hb2z hb3z hshift_z
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ := fullModN1Shift0V5_hmods_of_word_eq a b a0 a1 a2 a3 b0 hmodWord
  have hpath := evm_mod_n1_full_shift0_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_z halign
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n1_dispatchPre_to_pathEntry_v5 sp a b x1Val v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta modStackDispatchPostV5
    exact n1_shift0_modPost_to_modStackDispatchPost_v5 sp base a b a0 a1 a2 a3 b0 scratchMem
      ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq

/-- The full v5 n=1 MOD lane: combines the shift≠0 and shift=0 halves by
    `by_cases (clzResult b0).1 = 0`.  Mirror of `evm_div_n1_lane_v5`. -/
theorem evm_mod_n1_lane_v5 (sp base : Word) (a b : EvmWord)
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b0).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult b0).1 = 0
  · exact evm_mod_n1_lane_shift0_v5 sp base a b x1Val v5 v6 v7 v10 v11Old
      a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hb3z hb2z hb1z hsh halign
  · exact evm_mod_n1_lane_shiftNz_v5 sp base a b x1Val v5 v6 v7 v10 v11Old
      a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratch_un0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hb3z hb2z hb1z hsh halign

end EvmAsm.Evm64
