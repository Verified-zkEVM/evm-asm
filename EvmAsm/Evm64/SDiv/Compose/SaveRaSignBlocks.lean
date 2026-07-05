/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlocks

  SDIV wrapper composition for the saved-`ra` prologue followed by the
  dividend sign-bit probe.
-/

import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlockSpecs
import EvmAsm.Evm64.SDiv.Compose.SaveRaSignsPost

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_then_dividendSign_spec_in_sdivCodeV4
    (vRa vSavedOld sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 3 base ((base + dividendSignOff) + 8) (sdivCodeV4 base)
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop))) := by
  have hSave :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (by pcFree)
      (saveRa_spec_in_sdivCodeV4 vRa vSavedOld base)
  have hSign :=
    EvmAsm.Rv64.cpsTripleWithin_frameL
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))
      (by pcFree)
      (dividendSign_spec_in_sdivCodeV4 sp sOld dividendTop base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hSave hSign

end EvmAsm.Evm64.SDiv.Compose
