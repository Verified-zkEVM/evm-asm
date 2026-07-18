/-
  EvmAsm.EL.StorageEcallBridge

  Pure storage ECALL request/result surface for SLOAD and SSTORE (GH #110).
-/

import EvmAsm.EL.StorageAccessBridge

namespace EvmAsm.EL
namespace StorageEcallBridge

abbrev RvWord := BitVec 64
abbrev StorageAccessList := EvmAsm.Evm64.StorageAccess.StorageAccessList
abbrev Outcome := EvmAsm.Evm64.StorageAccessOutcome.Outcome

/-- Storage syscall selectors reserved for the EVM storage host interface. -/
inductive StorageSyscall where
  | sload
  | sstore
  deriving DecidableEq, Repr

/-- Selector value to put in the ECALL selector register for a storage syscall.
    These constants reserve a compact host-interface surface; later RV64 ECALL
    specs can connect them to concrete machine execution. -/
def selector : StorageSyscall → RvWord
  | .sload => 0xE0
  | .sstore => 0xE1

theorem selector_sload : selector .sload = (0xE0 : RvWord) := rfl

theorem selector_sstore : selector .sstore = (0xE1 : RvWord) := rfl

theorem selector_ne : selector .sload ≠ selector .sstore := by
  decide

end StorageEcallBridge
end EvmAsm.EL
