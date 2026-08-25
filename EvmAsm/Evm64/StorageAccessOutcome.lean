/-
  EvmAsm.Evm64.StorageAccessOutcome

  Pure SLOAD/SSTORE access outcomes for issue #119.
-/

module

public import EvmAsm.Evm64.StorageAccess

@[expose] public section

namespace EvmAsm.Evm64
namespace StorageAccessOutcome

/-- Dynamic gas and warm-list state produced by one storage-key access. -/
structure Outcome where
  status : StorageGas.StorageAccessStatus
  cost : Nat
  accesses : StorageAccess.StorageAccessList
  deriving Repr

def sloadOutcome
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    Outcome :=
  { status := StorageAccess.accessStatus accesses key
    cost := StorageAccess.sloadDynamicCostForKey accesses key
    accesses := StorageAccess.warmKey accesses key }

def sstoreOutcome
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    Outcome :=
  { status := StorageAccess.accessStatus accesses key
    cost := StorageAccess.sstoreDynamicCostForKey accesses key current new
    accesses := StorageAccess.warmKey accesses key }

theorem sloadOutcome_status
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    (sloadOutcome accesses key).status = StorageAccess.accessStatus accesses key := rfl

theorem sloadOutcome_cost
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    (sloadOutcome accesses key).cost =
      StorageAccess.sloadDynamicCostForKey accesses key := rfl

theorem sloadOutcome_warms
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey) :
    StorageAccess.isWarm (sloadOutcome accesses key).accesses key = true := by
  exact StorageAccess.warmKey_warms accesses key

theorem sstoreOutcome_status
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    (sstoreOutcome accesses key current new).status = StorageAccess.accessStatus accesses key := rfl

theorem sstoreOutcome_cost
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    (sstoreOutcome accesses key current new).cost =
      StorageAccess.sstoreDynamicCostForKey accesses key current new := rfl

theorem sstoreOutcome_warms
    (accesses : StorageAccess.StorageAccessList) (key : StorageAccess.StorageAccessKey)
    (current new : EvmWord) :
    StorageAccess.isWarm (sstoreOutcome accesses key current new).accesses key = true := by
  exact StorageAccess.warmKey_warms accesses key

theorem sloadOutcome_nil_cost (key : StorageAccess.StorageAccessKey) :
    (sloadOutcome [] key).cost = StorageGas.coldSloadCost := by
  simp [sloadOutcome]

theorem sstoreOutcome_nil_cost
    (key : StorageAccess.StorageAccessKey) (current new : EvmWord) :
    (sstoreOutcome [] key current new).cost =
      StorageGas.coldSloadCost + StorageGas.sstoreWriteCost current new := by
  simp [sstoreOutcome]

end StorageAccessOutcome
end EvmAsm.Evm64
