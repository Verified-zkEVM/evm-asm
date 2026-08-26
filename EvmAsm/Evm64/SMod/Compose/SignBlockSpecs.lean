/-
  EvmAsm.Evm64.SMod.Compose.SignBlockSpecs

  Primitive SMOD wrapper specs for sign-bit probe blocks.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseCode
public import EvmAsm.Evm64.SDiv.LimbSpec

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

theorem dividendSign_spec_in_smodCodeV4
    (sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + dividendSignOff) ((base + dividendSignOff) + 8)
      (smodCodeV4 base)
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop))
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x8
          EvmAsm.Evm64.evm_smodDividendTopLimbOff
          (base + dividendSignOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_dividendSign_sub (base := base) a i
      (by simpa [dividendSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x8
      EvmAsm.Evm64.evm_smodDividendTopLimbOff sp sOld dividendTop
      (base + dividendSignOff) (by decide))

theorem divisorSign_spec_in_smodCodeV4
    (sp sOld divisorTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff) ((base + divisorSignOff) + 8)
      (smodCodeV4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
         divisorTop))
      ((.x12 ↦ᵣ sp) **
       (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
         divisorTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x9
          EvmAsm.Evm64.evm_smodDivisorTopLimbOff
          (base + divisorSignOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_divisorSign_sub (base := base) a i
      (by simpa [divisorSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x9
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff sp sOld divisorTop
      (base + divisorSignOff) (by decide))

end EvmAsm.Evm64.SMod.Compose
