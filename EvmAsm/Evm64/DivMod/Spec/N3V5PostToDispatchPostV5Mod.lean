/-
  EvmAsm.Evm64.DivMod.Spec.N3V5PostToDispatchPostV5Mod

  N=3 V5 MOD: from `fullModN3UnifiedPostNoX1V5` (with exact caller `x1`) and the
  remainder-word correctness, conclude the scaffold post `modStackDispatchPostV5`.
  Thin mirror of `N2V5PostToDispatchPostV5Mod` over the n=3 callable-frame bridge
  (`N3V5ConcretePostBridgeMod`).
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5ConcretePostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.StackPostBridgeMod
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- From the n=3 v5 MOD unified post (with exact caller `x1`) and remainder-word
    correctness, conclude the scaffold post `modStackDispatchPostV5`. -/
theorem fullModN3UnifiedPostNoX1V5_to_modStackDispatchPostV5
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullModN3RemainderWordV5 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      modStackDispatchPostV5 sp a b h := by
  intro h hp
  have h1 := fullModN3UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
    bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hp
  simp only [modStackDispatchPostV5]
  revert h1
  apply sepConj_mono
  · exact fun h hp =>
      modStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h hp
  · exact fun h hp => memIs_implies_memOwn h hp

end EvmAsm.Evm64
