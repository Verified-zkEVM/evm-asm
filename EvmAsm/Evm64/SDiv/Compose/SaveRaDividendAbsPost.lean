/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPost

  Irreducible postcondition for the SDIV save-ra/signs/dividendAbs prefix.
-/

import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64.SDiv.Compose

/-- Postcondition for the SDIV save-ra/signs/dividendAbs prefix. Takes
    only the bare wrapper inputs; the sign/mask/sum/carry let-chain
    (~12 derived values) is computed internally so the theorem signature
    stays flat. Wrapped `@[irreducible]`. -/
@[irreducible]
def saveRaSignsThenDividendAbsPost
    (vRa sp divisorTop limb0 limb1 limb2 dividendTop : Word) : EvmAsm.Rv64.Assertion :=
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (dividendTop ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
    ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
   ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
    (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
    (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))

theorem saveRaSignsThenDividendAbsPost_unfold
    {vRa sp divisorTop limb0 limb1 limb2 dividendTop : Word} :
    saveRaSignsThenDividendAbsPost vRa sp divisorTop limb0 limb1 limb2 dividendTop =
      (let sign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (dividendTop ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
         (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))) := by
  delta saveRaSignsThenDividendAbsPost
  rfl

end EvmAsm.Evm64.SDiv.Compose
