/-
  EvmAsm.Evm64.SMod.Compose.SavedRaRet

  Low-level SMOD wrapper spec for the final saved-`ra` return instruction.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseCode

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

theorem savedRaRet_spec_in_smodCodeV4
    (vSavedRa : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + savedRaRetOff)
        ((vSavedRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~1)
      (smodCodeV4 base)
      (.x18 ↦ᵣ vSavedRa)
      (.x18 ↦ᵣ vSavedRa) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_smod_saved_ra_ret_block_code .x18
          (base + savedRaRetOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_savedRaRet_sub (base := base) a i
      (by simpa [savedRaRetCode,
        EvmAsm.Evm64.evm_smod_saved_ra_ret_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_smod_saved_ra_ret_block_spec_within .x18
      vSavedRa (base + savedRaRetOff))

end EvmAsm.Evm64.SMod.Compose
