/-
  EvmAsm.Evm64.SMod.Compose.BaseSpecsV5

  v5 SMOD wrapper-block leaf specs over `smodCodeV5`.  Each is a verbatim mirror
  of the corresponding `_in_smodCodeV4` spec (SavedRaRet.lean / ModCall.lean),
  lifted from `smodCodeV4` → `smodCodeV5` via the banked `smodCodeV5_*_sub`
  subsumptions (BaseCodeV5.lean).  The underlying block programs and their
  `evm_smod_*_block_spec_within` lemmas are code-agnostic, so only the code
  surface changes.  Foothold for the SMOD `.proven` flip over
  `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
import EvmAsm.Evm64.SMod.Compose.SavedRaRet
import EvmAsm.Evm64.SMod.Compose.ModCall

namespace EvmAsm.Evm64.SMod.Compose

/-- v5 mirror of `savedRaRet_spec_in_smodCodeV4`. -/
theorem savedRaRet_spec_in_smodCodeV5
    (vSavedRa : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + savedRaRetOff)
        ((vSavedRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~1)
      (smodCodeV5 base)
      (.x18 ↦ᵣ vSavedRa)
      (.x18 ↦ᵣ vSavedRa) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_smod_saved_ra_ret_block_code .x18
          (base + savedRaRetOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_savedRaRet_sub (base := base) a i
      (by simpa [savedRaRetCode,
        EvmAsm.Evm64.evm_smod_saved_ra_ret_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_smod_saved_ra_ret_block_spec_within .x18
      vSavedRa (base + savedRaRetOff))

/-- v5 mirror of `modCall_spec_in_smodCodeV4`. -/
theorem modCall_spec_in_smodCodeV5
    (vOld : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
        ((base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff)
      (smodCodeV5 base)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ ((base + modCallOff) + 4)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_div_call_block_code
          EvmAsm.Evm64.evm_smodCallOff (base + modCallOff)) a = some i →
        (smodCodeV5 base) a = some i := by
    intro a i h
    exact smodCodeV5_modCall_sub (base := base) a i
      (by simpa [modCallCode,
        EvmAsm.Evm64.evm_sdiv_div_call_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_div_call_block_spec_within
      EvmAsm.Evm64.evm_smodCallOff vOld (base + modCallOff))

end EvmAsm.Evm64.SMod.Compose
