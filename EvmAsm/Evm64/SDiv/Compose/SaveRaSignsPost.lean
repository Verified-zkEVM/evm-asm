/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaSignsPost

  Irreducible postcondition for the SDIV save-ra/dividend-sign/divisor-sign
  prefix.
-/

import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SDiv.Compose.SaveRaSignsPre

namespace EvmAsm.Evm64.SDiv.Compose

/-- Postcondition for the save-ra + dividend sign + divisor sign
    composition: `ra` is saved to the spill slot, `x8` and `x9` hold
    the dividend/divisor sign bits, and the top-limb memory cells are
    unchanged. Wrapped `@[irreducible]`. -/
@[irreducible]
def saveRaDividendSignThenDivisorSignPost
    (vRa sp dividendTop divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
    ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
       dividendTop))) **
   ((.x12 ↦ᵣ sp) **
    (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
    ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
      divisorTop))

theorem saveRaDividendSignThenDivisorSignPost_unfold
    {vRa sp dividendTop divisorTop : Word} :
    saveRaDividendSignThenDivisorSignPost vRa sp dividendTop divisorTop =
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       ((.x12 ↦ᵣ sp) **
        (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))) := by
  delta saveRaDividendSignThenDivisorSignPost
  rfl

end EvmAsm.Evm64.SDiv.Compose
