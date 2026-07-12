/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPre

  Irreducible precondition for the SDIV save-ra/signs/dividendAbs prefix.
-/

import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV save-ra + dividend/divisor signs +
    dividendAbs prefix. Takes only the bare wrapper inputs; the
    `sp`-relative dividend/divisor memory addresses are computed
    internally so the let-chain that previously lived in the theorem
    signature stays hidden inside this `@[irreducible]` def. -/
@[irreducible]
def saveRaSignsThenDividendAbsPre
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld
      limb0 limb1 limb2 dividendTop : Word) : EvmAsm.Rv64.Assertion :=
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
     ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
    ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
   (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
     (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
    ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))

theorem saveRaSignsThenDividendAbsPre_unfold
    {vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld
      limb0 limb1 limb2 dividendTop : Word} :
    saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
        maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop =
      (let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
          ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
         ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))) := by
  delta saveRaSignsThenDividendAbsPre
  rfl

end EvmAsm.Evm64.SDiv.Compose
