/-
  EvmAsm.Evm64.StorageAccessWarm

  Reusable warm-set facts for EIP-2929 storage accesses (GH #119).
-/

module

public import EvmAsm.Evm64.StorageAccess

@[expose] public section

namespace EvmAsm.Evm64
namespace StorageAccess

/-- Warming a key twice is the same as warming it once.
    Distinctive token: StorageAccessWarm.warmKey_idempotent #119. -/
theorem warmKey_idempotent (accesses : StorageAccessList) (key : StorageAccessKey) :
    warmKey (warmKey accesses key) key = warmKey accesses key := by
  exact warmKey_of_warm (warmKey_warms accesses key)

/-- Warming one key preserves any key that was already warm. -/
theorem isWarm_warmKey_of_isWarm
    {accesses : StorageAccessList} {key other : StorageAccessKey}
    (h_warm : isWarm accesses other = true) :
    isWarm (warmKey accesses key) other = true := by
  cases h_key : isWarm accesses key with
  | false =>
      simp [isWarm] at h_key h_warm ⊢
      simp [warmKey, isWarm, h_key, h_warm]
  | true =>
      simpa [warmKey, h_key] using h_warm

/-- Warming a key never makes a subsequent access to an already-warm key cold. -/
theorem accessStatus_warmKey_of_isWarm
    {accesses : StorageAccessList} {key other : StorageAccessKey}
    (h_warm : isWarm accesses other = true) :
    accessStatus (warmKey accesses key) other = .warm := by
  exact accessStatus_of_warm (isWarm_warmKey_of_isWarm h_warm)

/-- Once a key is warm, warming any key preserves the warm SLOAD dynamic cost. -/
theorem sloadDynamicCostForKey_warmKey_of_isWarm
    {accesses : StorageAccessList} {key other : StorageAccessKey}
    (h_warm : isWarm accesses other = true) :
    sloadDynamicCostForKey (warmKey accesses key) other =
      StorageGas.warmStorageReadCost := by
  exact sloadDynamicCostForKey_of_warm (isWarm_warmKey_of_isWarm h_warm)

end StorageAccess
end EvmAsm.Evm64
