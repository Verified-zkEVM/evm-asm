/-
  EvmAsm.Evm64.SMod.Compose.AbsBlockSpecs

  Primitive SMOD wrapper specs for the in-place absolute-value blocks.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseCode
public import EvmAsm.Evm64.SDiv.LimbSpec

public section

namespace EvmAsm.Evm64.SMod.Compose

theorem dividendAbs_spec_in_smodCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (smodCodeV4 base)
      (EvmAsm.Evm64.condNegate256BlockPre .x12 .x8 .x10 .x7 .x11
        0 8 16 24 sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3)
      (EvmAsm.Evm64.condNegate256BlockPost .x12 .x8 .x10 .x7 .x11
        0 8 16 24 sp sign limb0 limb1 limb2 limb3) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide))

theorem divisorAbs_spec_in_smodCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (smodCodeV4 base)
      (EvmAsm.Evm64.condNegate256BlockPre .x12 .x9 .x10 .x7 .x11
        32 40 48 56 sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3)
      (EvmAsm.Evm64.condNegate256BlockPost .x12 .x9 .x10 .x7 .x11
        32 40 48 56 sp sign limb0 limb1 limb2 limb3) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x9 .x10 .x7 .x11 32 40 48 56
          (base + divisorAbsOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_divisorAbs_sub (base := base) a i
      (by simpa [divisorAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide))

end EvmAsm.Evm64.SMod.Compose
