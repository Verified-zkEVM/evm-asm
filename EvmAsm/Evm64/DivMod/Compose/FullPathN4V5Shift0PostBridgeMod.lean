/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5Shift0PostBridgeMod

  The n=4 v5 shift=0 MOD lane post-bridge (generic, structural): from the n=4
  shift=0 MOD full-path output (the shift=0 MOD epilogue post — the raw mulsub
  remainder `r0..r3` copied into the `sp+32..56` output slots, plus the loop
  registers and the residual scratch frame) to `modStackDispatchPostV5 sp a b`,
  GIVEN the remainder-correctness facts `(EvmWord.mod a b).getLimbN k = rk`.  MOD
  mirror of `n4_shift0_post_to_divStackDispatchPost_v5`
  (FullPathN4V5Shift0PostBridge): where DIV reads a single-limb quotient `qVal`
  (limbs 1,2,3 zero), MOD reads the full 4-limb remainder from the output slots.
  Both shift=0 call branches (skip/addback) instantiate it with their `r`/scratch.
-/

import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Generic structural post-bridge for the n=4 v5 shift=0 MOD call paths: the
    shift=0 MOD epilogue output (4-limb remainder `r0..r3` in the `sp+32..56`
    output slots) plus the residual scratch frame implies
    `modStackDispatchPostV5 sp a b`, given that the stored remainder matches
    `EvmWord.mod a b`. -/
theorem n4_shift0_post_to_modStackDispatchPost_v5
    (sp : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (r0 r1 r2 r3 v9Val x11V u4V shiftV : Word)
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
       (.x9 ↦ᵣ v9Val) ** (.x11 ↦ᵣ x11V) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4088) ↦ₘ x11V) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4024) ↦ₘ u4V) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3968) ↦ₘ retMemV) ** ((sp + signExtend12 3960) ↦ₘ dMemV) **
       ((sp + signExtend12 3952) ↦ₘ dloMemV) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0V) **
       ((sp + signExtend12 3936) ↦ₘ scratchOutV) ** regOwn .x1) h →
      modStackDispatchPostV5 sp a b h := by
  intro h hp
  rw [modStackDispatchPostV5]
  rw [word_add_zero] at hp
  apply sepConj_mono_right (P := modStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (modStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _ hmod0 hmod1 hmod2 hmod3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
