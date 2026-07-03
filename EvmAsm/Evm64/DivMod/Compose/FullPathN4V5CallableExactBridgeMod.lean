/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExactBridgeMod

  Callable exact-frame post bridge for the n=4 v5 MOD lane.  MOD mirror of the
  DIV `n4_denormDivPost_frame_to_divStackDispatchPostCallableExactFrame_v5`
  (FullPathN4V5CallableExactBridge): lands `modStackDispatchPostCallableExactFrame`
  (concrete `x1 = raVal`, `x9 = x9Val`) via
  `modConcretePostNoX1ExactRegs_weaken_callable_frame`, from the `denormModPost`
  remainder-readout post + residual scratch frame with `x1 = raVal` concrete.
  Structurally = the dispatched `n4_denormModPost_frame_to_modStackDispatchPost_v5`
  (FullPathN4V5NoNopDispatchPostBridgeMod) but keeping `x1` concrete instead of
  weakening to `regOwn .x1` / `modStackDispatchPostV5`.  Toward `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5Mod
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Callable exact-frame twin of `n4_denormModPost_frame_to_modStackDispatchPost_v5`:
    the `denormModPost` remainder-readout post + residual scratch frame with
    concrete `x1 = raVal` implies
    `modStackDispatchPostCallableExactFrame sp a b raVal x9Val ** memOwn (sp+3936)`,
    given the four `(EvmWord.mod a b).getLimbN` facts. -/
theorem n4_denormModPost_frame_to_modStackDispatchPostCallableExactFrame_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (shift u0 u1 u2 u3 u4f qHatV x9Val raVal dMemV dloMemV scratchUn0V scratchOutV : Word)
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
       (sp + signExtend12 3936 ↦ₘ scratchOutV) ** (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal x9Val **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  delta denormModPost at hp
  rw [word_add_zero] at hp
  rw [modStackDispatchPostCallableExactFrame_unfold]
  apply sepConj_mono_right
    (P := (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** (.x9 ↦ᵣ x9Val))
    memIs_implies_memOwn h
  apply sepConj_mono_left (modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b) h
  rw [modConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ hmod0 hmod1 hmod2 hmod3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hp

/-- Callable exact-frame twin of `n4_shift0_post_to_modStackDispatchPost_v5`:
    the shift=0 MOD epilogue output (4-limb remainder `r0..r3` in the output
    slots) + residual scratch frame with concrete `x1 = raVal` implies
    `modStackDispatchPostCallableExactFrame sp a b raVal x9Val ** memOwn (sp+3936)`. -/
theorem n4_shift0_post_to_modStackDispatchPostCallableExactFrame_v5
    (sp : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (r0 r1 r2 r3 x9Val raVal x11V u4V shiftV : Word)
    (retMemV dMemV dloMemV scratchUn0V scratchOutV : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 = r0)
    (hmod1 : (EvmWord.mod a b).getLimbN 1 = r1)
    (hmod2 : (EvmWord.mod a b).getLimbN 2 = r2)
    (hmod3 : (EvmWord.mod a b).getLimbN 3 = r3) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0) ** (.x6 ↦ᵣ r1) ** (.x7 ↦ᵣ r2) **
       (.x2 ↦ᵣ r3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r3) **
       ((sp + signExtend12 3992) ↦ₘ shiftV) **
       ((sp + signExtend12 4056) ↦ₘ r0) ** ((sp + signExtend12 4048) ↦ₘ r1) **
       ((sp + signExtend12 4040) ↦ₘ r2) ** ((sp + signExtend12 4032) ↦ₘ r3) **
       ((sp + 32) ↦ₘ r0) ** ((sp + 40) ↦ₘ r1) **
       ((sp + 48) ↦ₘ r2) ** ((sp + 56) ↦ₘ r3) **
       (.x9 ↦ᵣ x9Val) ** (.x11 ↦ᵣ x11V) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4088) ↦ₘ x11V) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4024) ↦ₘ u4V) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3968) ↦ₘ retMemV) ** ((sp + signExtend12 3960) ↦ₘ dMemV) **
       ((sp + signExtend12 3952) ↦ₘ dloMemV) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0V) **
       ((sp + signExtend12 3936) ↦ₘ scratchOutV) ** (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal x9Val **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [word_add_zero] at hp
  rw [modStackDispatchPostCallableExactFrame_unfold]
  apply sepConj_mono_right
    (P := (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** (.x9 ↦ᵣ x9Val))
    memIs_implies_memOwn h
  apply sepConj_mono_left (modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b) h
  rw [modConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ hmod0 hmod1 hmod2 hmod3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
