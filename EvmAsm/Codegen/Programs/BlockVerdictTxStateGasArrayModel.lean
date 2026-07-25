/-
  Shared pure intrinsic-state-gas fact for the surviving
  `tx_intrinsic_state_gas` leaf proof. The retired array replay formerly
  consumed this fact alongside a separate EIP-7702 reconstruction; the live
  inline AccountState path now owns that transaction-boundary accounting.
-/

import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Stateless.SpecRef.Transactions

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel

open EvmAsm.Stateless.SpecRef

/-! ## Constants (re-export for callers) -/

/-- `StateGasCosts.AUTH_BASE` — net-new delegation indicator write. -/
abbrev authBase : Nat := StateGasCosts.AUTH_BASE

/-- `StateGasCosts.NEW_ACCOUNT` — authority leaf materialization. -/
abbrev newAccount : Nat := StateGasCosts.NEW_ACCOUNT

/-! ## Intrinsic state gas (post EIP-2780) -/

/-- Success-path pure intrinsic state gas for an encoded tx.

    Matches SpecRef `calculate_intrinsic_cost(...).state = 0` and the guest
    `tx_intrinsic_state_gas` body (accumulator 0 → `eip8037_tx_state_gas`).
    Parse failures are *not* modeled here — the array prog surfaces them as
    status a0 ∈ {1,2,3} without a success claim on `out[]`. -/
def pureIntrinsicStateGasSuccess : Nat := 0

theorem pureIntrinsicStateGasSuccess_eq_specRef
    (tx : Transaction) (sender : Address) :
    (calculate_intrinsic_cost tx sender).state = pureIntrinsicStateGasSuccess := by
  simp [calculate_intrinsic_cost, pureIntrinsicStateGasSuccess]

end EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
