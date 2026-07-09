/-
  EvmAsm.EL.StorageStackBridge

  Stack-facing bridge for SLOAD/SSTORE storage executions (GH #110).
-/

import EvmAsm.EL.StorageAccessBridge

namespace EvmAsm.EL

namespace StorageStackBridge

/-- SLOAD pushes one stack word. -/
def sloadResultCount : Nat := 1

/-- SSTORE pushes no stack words. -/
def sstoreResultCount : Nat := 0

/-- SSTORE's stack result payload is empty; state and access outcome are kept in
    `SstoreExecution`. -/
def sstoreStackWords (_execution : SstoreExecution) : List Word256 :=
  []

theorem sloadResultCount_eq_one :
    sloadResultCount = 1 := rfl

theorem sstoreResultCount_eq_zero :
    sstoreResultCount = 0 := rfl

end StorageStackBridge

end EvmAsm.EL
