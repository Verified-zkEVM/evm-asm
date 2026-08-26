/-
  EvmAsm.Evm64.DivMod.Spec.N3V5PostToDispatchPostV5

  N=3 V5 post bridge to the scaffold post `divStackDispatchPostV5`
  (= `divStackDispatchPost ** memOwn (sp+3936)`).  Composes the concrete-frame
  bridge (`fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word`,
  #7496-adjacent / 9.3.3.7) with the public weakening
  `divStackDispatchPostCallableExactFrame_weaken` and `memIs_implies_memOwn`.  This
  is the post half of the n=3 lane (the form `evm_div_stack_spec_unconditional_of_lanes_v5_div`
  consumes), mirroring n=2's `fullDivN2UnifiedPostNoX1V5_to_divStackDispatchPostV5`.
  Bead `evm-asm-wbc4i.9.3.3.4`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V5ConcretePostBridge
public import EvmAsm.Evm64.DivMod.Spec.StackPostBridge
public import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- From the n=3 v5 unified post (with exact caller `x1`) and quotient-word
    correctness, conclude the scaffold post `divStackDispatchPostV5`. -/
theorem fullDivN3UnifiedPostNoX1V5_to_divStackDispatchPostV5
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN3QuotientWordV5 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      divStackDispatchPostV5 sp a b h := by
  intro h hp
  have h1 := fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
    bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hp
  simp only [divStackDispatchPostV5]
  revert h1
  apply sepConj_mono
  · exact fun h hp =>
      divStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h hp
  · exact fun h hp => memIs_implies_memOwn h hp

end EvmAsm.Evm64
