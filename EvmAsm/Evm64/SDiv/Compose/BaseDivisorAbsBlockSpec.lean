/-
  EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsBlockSpec

  Leaf SDIV wrapper spec for the divisor absolute-value block.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsSequence

namespace EvmAsm.Evm64.SDiv.Compose

theorem divisorAbs_spec_in_sdivCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (sdivCodeV4 base)
      (divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (divisorAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [divisorAbsPre_unfold, divisorAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x9 .x10 .x7 .x11 32 40 48 56
          (base + divisorAbsOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_divisorAbs_sub (base := base) a i
      (by simpa [divisorAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose
