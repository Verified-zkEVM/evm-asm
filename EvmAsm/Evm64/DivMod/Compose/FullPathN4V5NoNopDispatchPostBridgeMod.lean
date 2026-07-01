/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridgeMod

  n=4 v5 MOD post bridge: the `denormModPost`-form full-path post (remainder
  readout) + residual scratch frame implies `modStackDispatchPostV5`, given the
  four per-limb `(EvmWord.mod a b).getLimbN` facts.  MOD mirror of
  `n4_denormDivPost_frame_to_divStackDispatchPost_v5`
  (FullPathN4V5NoNopDispatchPostBridge): `denormModPost` (remainder in the output
  cells) where DIV has `denormDivPost` (quotient), and the `mod`-limb facts where
  DIV threads `div`-limb facts.  The frame is generalized (branch-independent) so
  both the call-skip and call-addback lanes reuse it.
-/

import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- n=4 v5 MOD post bridge: `denormModPost` full-path post + residual frame implies
    `modStackDispatchPostV5`, given the four `(EvmWord.mod a b).getLimbN` facts. -/
theorem n4_denormModPost_frame_to_modStackDispatchPost_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (shift u0 u1 u2 u3 u4f qHatV x9Val dMemV dloMemV scratchUn0V scratchOutV : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (u0 >>> (shift.toNat % 64)) ||| (u1 <<< ((signExtend12 (0 : BitVec 12) - shift).toNat % 64)))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (u1 >>> (shift.toNat % 64)) ||| (u2 <<< ((signExtend12 (0 : BitVec 12) - shift).toNat % 64)))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (u2 >>> (shift.toNat % 64)) ||| (u3 <<< ((signExtend12 (0 : BitVec 12) - shift).toNat % 64)))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 = u3 >>> (shift.toNat % 64)) :
    ∀ h,
      (denormModPost sp shift u0 u1 u2 u3 **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + signExtend12 4088) ↦ₘ qHatV) **
       ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4f) **
       (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
       (.x9 ↦ᵣ x9Val) ** (.x11 ↦ᵣ qHatV) **
       (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
       (sp + signExtend12 3960 ↦ₘ dMemV) **
       (sp + signExtend12 3952 ↦ₘ dloMemV) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0V) **
       (sp + signExtend12 3936 ↦ₘ scratchOutV) ** regOwn .x1) h →
      modStackDispatchPostV5 sp a b h := by
  intro h hp
  rw [modStackDispatchPostV5]
  delta denormModPost at hp
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := modStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (modStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ hmod0 hmod1 hmod2 hmod3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
