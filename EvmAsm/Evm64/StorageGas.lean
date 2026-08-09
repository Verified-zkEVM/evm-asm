/-
  EvmAsm.Evm64.StorageGas

  Pure cold/warm storage access gas helpers for issue #119.
-/

import EvmAsm.Evm64.EvmWord
import EvmAsm.Evm64.GasCost

namespace EvmAsm.Evm64
namespace StorageGas

/-- EIP-2929 storage access status before an SLOAD/SSTORE key access. -/
inductive StorageAccessStatus where
  | cold
  | warm
  deriving DecidableEq, Repr

/-- Current Amsterdam cold SLOAD/storage-key access cost
    (`GasCosts.COLD_STORAGE_ACCESS`). -/
def coldSloadCost : Nat := 3000

/-- Current Amsterdam warm storage read/access cost (`GasCosts.WARM_ACCESS`). -/
def warmStorageReadCost : Nat := 100

/-- Dynamic gas charged for the storage-key access itself. -/
def storageAccessCost : StorageAccessStatus → Nat
  | .cold => coldSloadCost
  | .warm => warmStorageReadCost

/-- Dynamic SLOAD cost is exactly the cold/warm storage-key access cost. -/
def sloadDynamicCost (status : StorageAccessStatus) : Nat :=
  storageAccessCost status

/-- Warm SSTORE no-op cost: writing the same value charges a warm storage read. -/
def sstoreNoopCost : Nat := warmStorageReadCost

/-- Warm SSTORE cost when a zero slot is set to a nonzero value.

The regular component is `GasCosts.STORAGE_WRITE` from
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py:73-75`; the state
component is `StateGasCosts.STORAGE_SET` from
`execution-specs/src/ethereum/forks/amsterdam/vm/gas.py:40-46`, namely 64
state bytes at 1,530 gas per byte. -/
def sstoreSetCost : GasCost :=
  { regular := 10000
    state := 64 * 1530 }

/-- Warm SSTORE cost when a nonzero slot is written to a different value. -/
def sstoreResetCost : Nat := 10000

/-- EIP-2929 cold-key surcharge for SSTORE. Warm keys have no surcharge. -/
def sstoreColdSurcharge : StorageAccessStatus → Nat
  | .cold => coldSloadCost
  | .warm => 0

/-- Warm-key SSTORE write cost, before any cold-key surcharge or refund logic. -/
def sstoreWriteCost (current new : EvmWord) : Nat :=
  if new = current then
    sstoreNoopCost
  else if current = 0 then
    sstoreSetCost.regular
  else
    sstoreResetCost

/-- Dynamic SSTORE cost surface: cold-key surcharge plus warm write cost. -/
def sstoreDynamicCost (status : StorageAccessStatus) (current new : EvmWord) : Nat :=
  sstoreColdSurcharge status + sstoreWriteCost current new

/-- After any storage-key access, that key is warm for the rest of the transaction. -/
def warmAfterAccess (_status : StorageAccessStatus) : StorageAccessStatus :=
  .warm

@[simp] theorem storageAccessCost_cold :
    storageAccessCost .cold = coldSloadCost := rfl

@[simp] theorem storageAccessCost_warm :
    storageAccessCost .warm = warmStorageReadCost := rfl

@[simp] theorem sloadDynamicCost_cold :
    sloadDynamicCost .cold = coldSloadCost := rfl

@[simp] theorem sloadDynamicCost_warm :
    sloadDynamicCost .warm = warmStorageReadCost := rfl

@[simp] theorem sstoreColdSurcharge_cold :
    sstoreColdSurcharge .cold = coldSloadCost := rfl

@[simp] theorem sstoreColdSurcharge_warm :
    sstoreColdSurcharge .warm = 0 := rfl

theorem sstoreWriteCost_noop (current : EvmWord) :
    sstoreWriteCost current current = sstoreNoopCost := by
  simp [sstoreWriteCost]

theorem sstoreWriteCost_set {new : EvmWord} (h_new : new ≠ 0) :
    sstoreWriteCost 0 new = sstoreSetCost.regular := by
  unfold sstoreWriteCost
  split
  · contradiction
  · simp

theorem sstoreWriteCost_reset {current new : EvmWord}
    (h_current : current ≠ 0) (h_ne : new ≠ current) :
    sstoreWriteCost current new = sstoreResetCost := by
  unfold sstoreWriteCost
  split
  · contradiction
  · rfl

theorem sstoreDynamicCost_warm (current new : EvmWord) :
    sstoreDynamicCost .warm current new = sstoreWriteCost current new := by
  simp [sstoreDynamicCost]

theorem sstoreDynamicCost_cold (current new : EvmWord) :
    sstoreDynamicCost .cold current new =
      coldSloadCost + sstoreWriteCost current new := rfl

@[simp] theorem warmAfterAccess_cold :
    warmAfterAccess .cold = .warm := rfl

@[simp] theorem warmAfterAccess_warm :
    warmAfterAccess .warm = .warm := rfl

@[simp] theorem warmAfterAccess_eq_warm (status : StorageAccessStatus) :
    warmAfterAccess status = .warm := by
  cases status <;> rfl

theorem storageAccessCost_cold_eq :
    storageAccessCost .cold = 3000 := rfl

theorem storageAccessCost_warm_eq :
    storageAccessCost .warm = 100 := rfl

theorem sloadDynamicCost_cold_eq :
    sloadDynamicCost .cold = 3000 := rfl

theorem sloadDynamicCost_warm_eq :
    sloadDynamicCost .warm = 100 := rfl

theorem sstoreNoopCost_eq :
    sstoreNoopCost = 100 := rfl

theorem sstoreSetCost_components :
    sstoreSetCost.regular = 10000 ∧ sstoreSetCost.state = 97920 := by
  constructor <;> rfl

theorem sstoreResetCost_eq :
    sstoreResetCost = 10000 := rfl

end StorageGas
end EvmAsm.Evm64
