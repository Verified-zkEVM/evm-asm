/-
  EvmAsm.Evm64.StorageGas

  Pure cold/warm storage access gas helpers for issue #119.
-/

namespace EvmAsm.Evm64
namespace StorageGas

/-- EIP-2929 storage access status before an SLOAD/SSTORE key access. -/
inductive StorageAccessStatus where
  | cold
  | warm
  deriving DecidableEq, Repr

/-- Cold SLOAD/storage-key access cost from EIP-2929. -/
def coldSloadCost : Nat := 2100

/-- Warm storage read/access cost from EIP-2929. -/
def warmStorageReadCost : Nat := 100

/-- Dynamic gas charged for the storage-key access itself. -/
def storageAccessCost : StorageAccessStatus → Nat
  | .cold => coldSloadCost
  | .warm => warmStorageReadCost

/-- Dynamic SLOAD cost is exactly the cold/warm storage-key access cost. -/
def sloadDynamicCost (status : StorageAccessStatus) : Nat :=
  storageAccessCost status

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

@[simp] theorem warmAfterAccess_cold :
    warmAfterAccess .cold = .warm := rfl

@[simp] theorem warmAfterAccess_warm :
    warmAfterAccess .warm = .warm := rfl

@[simp] theorem warmAfterAccess_eq_warm (status : StorageAccessStatus) :
    warmAfterAccess status = .warm := by
  cases status <;> rfl

theorem storageAccessCost_cold_eq :
    storageAccessCost .cold = 2100 := rfl

theorem storageAccessCost_warm_eq :
    storageAccessCost .warm = 100 := rfl

theorem sloadDynamicCost_cold_eq :
    sloadDynamicCost .cold = 2100 := rfl

theorem sloadDynamicCost_warm_eq :
    sloadDynamicCost .warm = 100 := rfl

end StorageGas
end EvmAsm.Evm64
