/-
  EvmAsm.Evm64.SMod.Compose.PreserveDividendSign

  Low-level SMOD wrapper spec for preserving the dividend sign across the
  nested MOD callable.
-/

module

public import EvmAsm.Evm64.SMod.Compose.BaseCode

public section

namespace EvmAsm.Evm64.SMod.Compose

theorem preserveDividendSign_spec_in_smodCodeV4
    (dividendSign x13Old : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 1 (base + preserveDividendSignOff)
      ((base + preserveDividendSignOff) + 4)
      (smodCodeV4 base)
      ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ x13Old))
      ((.x8 ↦ᵣ dividendSign) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Rv64.CodeReq.singleton (base + preserveDividendSignOff)
          (.ADDI .x13 .x8 0)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_preserveDividendSign_sub (base := base) a i
      (by
        rw [preserveDividendSignCode, EvmAsm.Rv64.ADDI,
          EvmAsm.Rv64.single, EvmAsm.Rv64.CodeReq.ofProg_singleton]
        exact h)
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono
    (EvmAsm.Rv64.addi_spec_within .x13 .x8 dividendSign x13Old
      0 (base + preserveDividendSignOff) (by decide))

end EvmAsm.Evm64.SMod.Compose
