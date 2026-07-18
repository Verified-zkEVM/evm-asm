/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlockSpecs

  Primitive SDIV wrapper specs for the saved-`ra` prologue and sign-bit
  probe blocks.
-/

import EvmAsm.Evm64.SDiv.Compose.SignCodeSlices
import EvmAsm.Evm64.SDiv.LimbSpec

namespace EvmAsm.Evm64.SDiv.Compose

theorem saveRa_spec_in_sdivCodeV4
    (vRa vSavedOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 base (base + 4) (sdivCodeV4 base)
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i, (EvmAsm.Evm64.evm_sdiv_save_ra_block_code .x18 base) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_saveRa_sub (base := base) a i
      (by simpa [saveRaCode, saveRaOff,
        EvmAsm.Evm64.evm_sdiv_save_ra_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_save_ra_block_spec_within .x18
      vRa vSavedOld base (by decide))

theorem dividendSign_spec_in_sdivCodeV4
    (sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + dividendSignOff) ((base + dividendSignOff) + 8)
      (sdivCodeV4 base)
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x8
          EvmAsm.Evm64.evm_sdivDividendTopLimbOff
          (base + dividendSignOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_dividendSign_sub (base := base) a i
      (by simpa [dividendSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff sp sOld dividendTop
      (base + dividendSignOff) (by decide))

theorem divisorSign_spec_in_sdivCodeV4
    (sp sOld divisorTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff) ((base + divisorSignOff) + 8)
      (sdivCodeV4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         divisorTop))
      ((.x12 ↦ᵣ sp) **
       (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         divisorTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x9
          EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
          (base + divisorSignOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_divisorSign_sub (base := base) a i
      (by simpa [divisorSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff sp sOld divisorTop
      (base + divisorSignOff) (by decide))

end EvmAsm.Evm64.SDiv.Compose
