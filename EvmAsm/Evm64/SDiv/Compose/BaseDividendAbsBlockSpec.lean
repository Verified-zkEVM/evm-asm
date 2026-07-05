/-
  EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsBlockSpec

  Leaf SDIV wrapper spec for the dividend absolute-value block.
-/

import EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPost

namespace EvmAsm.Evm64.SDiv.Compose

theorem dividendAbs_spec_in_sdivCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (sdivCodeV4 base)
      (dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (dividendAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [dividendAbsPre_unfold, dividendAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose
