import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec

namespace EvmAsm.Codegen.ValidateHeaderGasCorrespondence

/-- `hslack : listLen + 9 ≤ bytes.length` at the `H+176` call site instantiates to
    `headerLen + 9 ≤ headerLen` (see issue #13234), which is false for every `headerLen`. -/
theorem extra_data_hslack_unsat : ∀ (headerLen : Nat), ¬ (headerLen + 9 ≤ headerLen) := by
  intro headerLen
  omega

end EvmAsm.Codegen.ValidateHeaderGasCorrespondence
