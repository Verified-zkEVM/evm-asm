/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShift0Mod

  The v5 n=3 MOD lane, shift=0 case: from the stack-dispatch precondition
  `divModStackDispatchPreNoX1` to `modStackDispatchPostV5`, over `modCode_noNop_v5`,
  given the normalization shift is zero (`clz b2 = 0`).  MOD mirror of
  `FullPathN3V5LaneShift0` (DIV): pins the two runtime borrow flags, composes the
  flag-param full shift=0 MOD path (`evm_mod_n3_full_shift0_param_v5_noNop`), the
  inline dispatch-pre adapter, and the shift=0 MOD post bridge — the latter routes
  through `modConcretePostNoX1ExactRegsFrame` (as the DIV shift=0 bridge does) to
  handle the `.x1 ↦ᵣ raVal` regIs → `regOwn .x1` weakening.  Fed the shift=0 MOD
  remainder correctness (`n3_shift0_remainder_word_eq_mod_lane`).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FullShift0Mod
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShiftNzMod
import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0ModRemainder
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.StackPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

open EvmWord in
/-- Project the shift=0 MOD remainder-word equality into the four per-limb
    `getLimbN` facts (in the folded `n3Shift0R0` form). -/
theorem n3_shift0_mod_getLimbN_threaded (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 : Word) (bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3z : b.getLimbN 3 = 0)
    (hb2ge : b2.toNat ≥ 2 ^ 63)
    (hc1 : bltu_1 = true → BitVec.ult (0 : Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0 : Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    (EvmWord.mod a b).getLimbN 0 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1 ∧
    (EvmWord.mod a b).getLimbN 1 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1 := by
  have hword := n3_shift0_remainder_word_eq_mod_lane a b a0 a1 a2 a3 b0 b1 b2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3z hb2ge hc1 hm1 hc0 hm0
  have h0 : (0 : Word).toNat = 0 := rfl
  have hvpos : 2 ^ 191 ≤ val256 b0 b1 b2 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a1 a2 a3 0 < 2 ^ 64 * val256 b0 b1 b2 0 := by
    have ha : val256 a1 a2 a3 0 < 2 ^ 192 := by
      have := a1.isLt; have := a2.isLt; have := a3.isLt
      simp only [EvmWord.val256, h0]; omega
    calc val256 a1 a2 a3 0 < 2 ^ 192 := ha
      _ ≤ 2 ^ 64 * 2 ^ 191 := by norm_num
      _ ≤ 2 ^ 64 * val256 b0 b1 b2 0 := Nat.mul_le_mul_left _ hvpos
  obtain ⟨hR1u4, _⟩ := iterN3V5_collapse bltu_1 b0 b1 b2 a1 a2 a3 0 hb2ge hfwv hc1 hm1
  -- Per goal (no `<;>`/`first`): unfold the `n3Shift0R0` RHS + collapse the u4 slot,
  -- then rewrite `mod a b` to the fromLimbs form and project. Mirrors the DIV
  -- `n3_shift0_div_getLimbN_threaded` structure.
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [n3Shift0R0, n3Shift0R1]; rw [hR1u4, ← hword]; exact EvmWord.getLimbN_fromLimbs_0
  · simp only [n3Shift0R0, n3Shift0R1]; rw [hR1u4, ← hword]; exact EvmWord.getLimbN_fromLimbs_1
  · simp only [n3Shift0R0, n3Shift0R1]; rw [hR1u4, ← hword]; exact EvmWord.getLimbN_fromLimbs_2
  · simp only [n3Shift0R0, n3Shift0R1]; rw [hR1u4, ← hword]; exact EvmWord.getLimbN_fromLimbs_3

/-- Shift=0 MOD post bridge: the shift=0 full-path post implies `modStackDispatchPostV5`,
    given the per-limb `mod` facts.  MOD mirror of `n3_shift0_fullPost_to_divStackDispatchPostV5`,
    routing through `modConcretePostNoX1ExactRegsFrame`. -/
theorem n3_shift0_modPost_to_modStackDispatchPost_v5
    (bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1)
    (hmod1 : (EvmWord.mod a b).getLimbN 1 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1)
    (hmod2 : (EvmWord.mod a b).getLimbN 2 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1)
    (hmod3 : (EvmWord.mod a b).getLimbN 3 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        (.x6 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        (.x7 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
        ((sp + signExtend12 4056) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        ((sp + signExtend12 4048) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        ((sp + signExtend12 4040) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        ((sp + signExtend12 4032) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        ((sp + 32) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1) **
        ((sp + 40) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1) **
        ((sp + 48) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1) **
        ((sp + 56) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1)) **
       (((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
         ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
         ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
         ((sp + signExtend12 4064) ↦ₘ (0 : Word))) **
       fullModN3FrameShift0V5Rest bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
         retMem dMem dloMem scratchUn0 scratchMem raVal) h →
      modStackDispatchPostV5 sp a b h := by
  intro h hq
  rw [fullModN3FrameShift0V5Rest_unfold] at hq
  have hExact :
      (modConcretePostNoX1ExactRegsFrame sp a b (signExtend12 4095) raVal
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1 (0 : Word) (0 : Word)
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.2
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.2.2.2 (0 : Word) (0 : Word)
        (clzResult b2).1 (3 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then b2 else if bltu_1 then b2 else dMem)
        (if bltu_0 then divKTrialCallV5DLo b2
          else if bltu_1 then divKTrialCallV5DLo b2 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0 (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.1
          else if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        (if bltu_0 then divKTrialCallV5ScratchOut (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.2.1
            (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.1 b2
            (if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem)
          else if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem))) h := by
    rw [modConcretePostNoX1ExactRegsFrame_unfold,
        evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
        evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
          hmod0 hmod1 hmod2 hmod3,
        divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
    rw [word_add_zero] at hq
    xperm_hyp hq
  rw [modStackDispatchPostV5]
  exact sepConj_mono
    (fun h hp => modStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h
      (by rw [modStackDispatchPostCallableExactFrame_unfold]
          exact modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp))
    (fun h hp => memIs_implies_memOwn h hp)
    h hExact

/-- The v5 n=3 MOD lane, shift=0: stack-dispatch precondition → `modStackDispatchPostV5`. -/
theorem evm_mod_n3_lane_shift0_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 2)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hb2ge : (b.getLimbN 2).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  obtain ⟨bltu_1, hbltu_1⟩ : ∃ x, x = BitVec.ult (0 : Word) (b.getLimbN 2) := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (iterN3V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) 0
          (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) 0 0).2.2.2.1
        (b.getLimbN 2) := ⟨_, rfl⟩
  have hc1 : bltu_1 = true → BitVec.ult (0 : Word) (b.getLimbN 2) = true :=
    fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false → ¬ BitVec.ult (0 : Word) (b.getLimbN 2) :=
    fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) 0
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) 0 0).2.2.2.1 (b.getLimbN 2) = true :=
    fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) 0
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) 0 0).2.2.2.1 (b.getLimbN 2) :=
    fun h => by rw [← hbltu_0, h]; decide
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ := n3_shift0_mod_getLimbN_threaded a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) bltu_1 bltu_0
    rfl rfl rfl rfl rfl rfl rfl hb3z hb2ge hc1 hm1 hc0 hm0
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| (0 : Word) ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  have hpath := evm_mod_n3_full_shift0_param_v5_noNop bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
    ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem raVal
    (signExtend12 (4 : BitVec 12) - (4 : Word)) hbnz' hb2nz hshift_z halign
    hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    rw [divModStackDispatchPreNoX1_unfold] at hp
    rw [show evmWordIs sp a =
        ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
         ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
        from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl]] at hp
    rw [show evmWordIs (sp + 32) b =
        (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
         ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3))
        from by rw [evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl]] at hp
    rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
    rw [hb3z] at hp
    simp only [word_add_zero]
    xperm_hyp hp
  · intro h hq
    exact n3_shift0_modPost_to_modStackDispatchPost_v5 bltu_1 bltu_0 sp base a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) retMem dMem dloMem scratch_un0 scratchMem raVal
      rfl rfl rfl rfl hmod0 hmod1 hmod2 hmod3 h hq

end EvmAsm.Evm64
