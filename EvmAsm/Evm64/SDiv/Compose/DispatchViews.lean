/-
  EvmAsm.Evm64.SDiv.Compose.DispatchViews

  Compatibility module for stack/result-sign view lemmas used by the SDIV
  div-call dispatch composition.
-/

import EvmAsm.Evm64.SDiv.Compose.DispatchStackViews
import EvmAsm.Evm64.SDiv.Compose.QuadMemBridges
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView

namespace EvmAsm.Evm64.SDiv.Compose

/-- General postcondition view for SDIV result-sign fixup: the four memory
    result limbs fold into a single `evmWordIs` for the named sign-fixed word,
    with scratch registers still exposed. -/
theorem resultSignFixPost_evmWordIs
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    resultSignFixPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
        (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
        evmWordIs sp (sdivSignFixedWord sign limb0 limb1 limb2 limb3))) := by
  rw [resultSignFixPost_unfold]
  dsimp only [sdivSignFixedWord, rippleNegWord]
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  change
    (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
       ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ sum3))) =
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sum0
        | 1 => sum1
        | 2 => sum2
        | 3 => sum3)))
  rw [evmWordIs_eq_quadMem_named]
  rfl

end EvmAsm.Evm64.SDiv.Compose
