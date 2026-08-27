/-
  EvmAsm.Evm64.SMod.Compose.ModCall

  Low-level SMOD wrapper spec for the near call into the appended unsigned
  MOD callable.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseCode
public import EvmAsm.Evm64.SDiv.LimbSpec

public section

namespace EvmAsm.Evm64.SMod.Compose

theorem modCall_spec_in_smodCodeV4
    (vOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
        ((base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff)
      (smodCodeV4 base)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ ((base + modCallOff) + 4)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_div_call_block_code
          EvmAsm.Evm64.evm_smodCallOff (base + modCallOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_modCall_sub (base := base) a i
      (by simpa [modCallCode,
        EvmAsm.Evm64.evm_sdiv_div_call_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_div_call_block_spec_within
      EvmAsm.Evm64.evm_smodCallOff vOld (base + modCallOff))

end EvmAsm.Evm64.SMod.Compose
