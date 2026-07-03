/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5LaneShiftNzMod

  The v5 n=3 MOD lane, shift≠0 case: from the stack-dispatch precondition
  `divModStackDispatchPreNoX1` to `modStackDispatchPostV5`, over `modCode_noNop_v5`.
  MOD mirror of `FullPathN3V5LaneShiftNz` (DIV n=3): composes the full entry→nopOff
  path with the carry discharged from shape
  (`evm_mod_n3_preloop_loop_denorm_v5_noNop_fromShape`) — bridged at the pre from
  `divModStackDispatchPreNoX1` (op-agnostic `evmWordIs`/`divScratchValuesCallNoX1`
  unfolds) — with the post bridge (`fullModN3UnifiedPostNoX1V5_to_modStackDispatchPostV5`)
  fed the shape-derived remainder correctness
  (`fullModN3RemainderWordV5_eq_mod_lane_of_shape`), and step-count widening to
  `unifiedDivBound`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopFullToNopOffMod
import EvmAsm.Evm64.DivMod.Spec.N3V5PostToDispatchPostV5Mod
import EvmAsm.Evm64.DivMod.Spec.N3V5QuotientLaneShapeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem evm_mod_n3_lane_shiftNz_v5 (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
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
  -- The two runtime borrow flags, in clean `ult (fullDivN3R1V5 …)` form.
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (fullDivN3R1V5 bltu_1 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := ⟨_, rfl⟩
  -- The per-digit `bltu` path matches, from the clean flag definitions.
  have hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 = true := fun h => by rw [← hbltu_1]; exact h
  have hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 := fun h => by rw [← hbltu_1, h]; decide
  have hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 = true := fun h => by rw [← hbltu_0]; exact h
  have hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
        (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1 := fun h => by rw [← hbltu_0, h]; decide
  -- Remainder correctness from shape (lane form).
  have hdivWord := fullModN3RemainderWordV5_eq_mod_lane_of_shape bltu_1 bltu_0
    (a := a) (b := b) rfl rfl rfl rfl rfl rfl rfl rfl
    hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  -- The limb-`or` form of `b ≠ 0`, derived from `b2 ≠ 0`.
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  -- The full entry→nopOff path with carry discharged from shape.
  have hpath := evm_mod_n3_preloop_loop_denorm_v5_noNop_fromShape bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem raVal
    (signExtend12 (4 : BitVec 12) - (4 : Word)) ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
    hbnz' hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0
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
    simp only [word_add_zero]
    xperm_hyp hp
  · -- post bridge.
    intro h hq
    exact fullModN3UnifiedPostNoX1V5_to_modStackDispatchPostV5 bltu_1 bltu_0 sp base a b
      retMem dMem dloMem scratch_un0 scratchMem raVal hdivWord h hq

end EvmAsm.Evm64
