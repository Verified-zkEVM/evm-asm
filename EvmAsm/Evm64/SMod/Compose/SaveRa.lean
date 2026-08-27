/-
  EvmAsm.Evm64.SMod.Compose.SaveRa

  Low-level SMOD wrapper spec for the saved-`ra` prologue instruction.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseCode

public section

namespace EvmAsm.Evm64.SMod.Compose

theorem saveRa_spec_in_smodCodeV4
    (vRa vSavedOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + saveRaOff) ((base + saveRaOff) + 4)
      (smodCodeV4 base)
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_smod_save_ra_block_code .x18
          (base + saveRaOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_saveRa_sub (base := base) a i
      (by simpa [saveRaCode,
        EvmAsm.Evm64.evm_smod_save_ra_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_smod_save_ra_block_spec_within .x18
      vRa vSavedOld (base + saveRaOff) (by decide))

end EvmAsm.Evm64.SMod.Compose
