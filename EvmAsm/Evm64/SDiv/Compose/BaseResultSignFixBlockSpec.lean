/-
  EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec

  SDIV wrapper base spec for the result sign-fixup block.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseCode
import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix

namespace EvmAsm.Evm64.SDiv.Compose

theorem resultSignFix_spec_in_sdivCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV4 base)
      (resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPre_unfold, resultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose
