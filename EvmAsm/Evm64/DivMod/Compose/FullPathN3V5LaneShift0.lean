/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShift0

  The v5 n=3 DIV lane, shift=0 case: from the stack-dispatch precondition
  `divModStackDispatchPreNoX1` to `divStackDispatchPostV5`, over `divCode_noNop_v5`,
  given the normalization shift is zero (`clz b2 = 0`).  Pins the two runtime borrow
  flags to their canonical `ult` values, then composes the flag-param full shift=0
  path (#7558), the inline dispatch-pre adapter (mirror of the shift≠0 lane #7550),
  and the shift=0 post bridge (#7559) fed the shift=0 quotient correctness (#7563).
  n=3 analog of `evm_div_n2_lane_shift0_v5`.  The shift=0 half of `lane_n3`.
  Bead `evm-asm-wbc4i.9.3.3.5` / `.9.3.3.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FullShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5DivLimbThreadedShift0
import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0PostBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem evm_div_n3_lane_shift0_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 2)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hb2ge : (b.getLimbN 2).toNat ≥ 2 ^ 63 := clz_zero_imp_msb hshift_z
  -- canonical flags (clean ult, threaded raw-window iterN3V5 form)
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
  -- quotient correctness from shape (n3Shift0R* form)
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := n3_shift0_div_getLimbN_threaded a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) bltu_1 bltu_0
    rfl rfl rfl rfl rfl rfl rfl hb3z hb2ge hc1 hm1 hc0 hm0
  -- limb-`or` form of `b ≠ 0`, from `b2 ≠ 0`
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| (0 : Word) ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  -- the flag-param full shift=0 path
  have hpath := evm_div_n3_full_shift0_param_v5_noNop bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
    ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem raVal
    (signExtend12 (4 : BitVec 12) - (4 : Word)) hbnz' hb2nz hshift_z halign
    hbltu_1 hbltu_0
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · -- pre-adapter: the dispatch pre unfolds to the explicit stack pre-state.
    intro h hp
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
  · -- post bridge.
    intro h hq
    exact n3_shift0_fullPost_to_divStackDispatchPostV5 bltu_1 bltu_0 sp base a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) retMem dMem dloMem scratch_un0 scratchMem raVal
      rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3 h hq

end EvmAsm.Evm64
