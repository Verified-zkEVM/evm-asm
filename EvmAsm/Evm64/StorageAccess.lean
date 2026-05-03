/-
  EvmAsm.Evm64.StorageAccess

  Pure storage access-list helpers for issue #119.
-/

import EvmAsm.Evm64.Environment
import EvmAsm.Evm64.StorageGas

namespace EvmAsm.Evm64
namespace StorageAccess

/-- Storage key touched by EIP-2929 cold/warm accounting. -/
structure StorageAccessKey where
  address : Address
  slot : EvmWord
  deriving DecidableEq, Repr

/-- Pure access-list model for storage keys already warmed in this transaction. -/
abbrev StorageAccessList := List StorageAccessKey

/-- Whether a storage key is already warm. -/
def isWarm (accesses : StorageAccessList) (key : StorageAccessKey) : Bool :=
  accesses.contains key

/-- Add a storage key to the warm set for subsequent accesses. -/
def warmKey (accesses : StorageAccessList) (key : StorageAccessKey) : StorageAccessList :=
  if isWarm accesses key then accesses else key :: accesses

/-- Cold/warm status for the next access to `key`. -/
def accessStatus (accesses : StorageAccessList) (key : StorageAccessKey) :
    StorageGas.StorageAccessStatus :=
  if isWarm accesses key then .warm else .cold

@[simp] theorem isWarm_nil (key : StorageAccessKey) :
    isWarm [] key = false := rfl

@[simp] theorem isWarm_cons_self (key : StorageAccessKey) (accesses : StorageAccessList) :
    isWarm (key :: accesses) key = true := by
  simp [isWarm]

theorem warmKey_warms (accesses : StorageAccessList) (key : StorageAccessKey) :
    isWarm (warmKey accesses key) key = true := by
  cases h_warm : isWarm accesses key <;> simp [warmKey, h_warm]

theorem warmKey_of_warm {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_warm : isWarm accesses key = true) :
    warmKey accesses key = accesses := by
  simp [warmKey, h_warm]

theorem accessStatus_of_warm {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_warm : isWarm accesses key = true) :
    accessStatus accesses key = .warm := by
  simp [accessStatus, h_warm]

theorem accessStatus_of_cold {accesses : StorageAccessList} {key : StorageAccessKey}
    (h_cold : isWarm accesses key = false) :
    accessStatus accesses key = .cold := by
  simp [accessStatus, h_cold]

@[simp] theorem accessStatus_nil (key : StorageAccessKey) :
    accessStatus [] key = .cold := by
  simp [accessStatus, isWarm]

theorem accessStatus_after_warmKey (accesses : StorageAccessList) (key : StorageAccessKey) :
    accessStatus (warmKey accesses key) key = .warm := by
  exact accessStatus_of_warm (warmKey_warms accesses key)

end StorageAccess
end EvmAsm.Evm64
