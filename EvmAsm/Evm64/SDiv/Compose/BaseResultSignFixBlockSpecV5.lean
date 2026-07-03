/-
  EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpecV5

  v5 mirror of the result-sign-fix block spec (`resultSignFix_spec_in_sdivCodeV4`
  in `BaseResultSignFixBlockSpec`), over `sdivCodeV5`.  The SDIV sign-fix return
  code lives in the shared `evm_sdiv_wrapper` prefix and is identical between the
  v4 and v5 wrappers (only the appended divider differs), so this is a verbatim
  swap of the code-region subsumption `sdivCodeV4_resultSignFix_sub` →
  `sdivCodeV5_resultSignFix_sub`.  Return-chain leaf toward SDIV `.proven`.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec
import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- v5 mirror of `resultSignFix_spec_in_sdivCodeV4`: the result-sign-fix block
    over `sdivCodeV5`. -/
theorem resultSignFix_spec_in_sdivCodeV5
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCodeV5 base)
      (resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPre_unfold, resultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (sdivCodeV5 base) a = some i := by
    intro a i h
    exact sdivCodeV5_resultSignFix_sub (base := base) a i
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
