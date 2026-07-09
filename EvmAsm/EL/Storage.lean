/-
  EvmAsm.EL.Storage

  Pure SLOAD/SSTORE semantics over the EL world-state model (GH #110 slice 1).
  Concrete ECALL interfaces and stack-level Evm64 opcode specs are layered on
  top of these definitions in later slices.
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL
namespace Storage

/-- Pure SLOAD: read one storage slot from an account. Missing slots are already
    modeled as zero by `WorldState.getStorage`. -/
def sload (state : WorldState) (addr : Address) (key : StorageKey) : Word256 :=
  state.getStorage addr key

/-- Pure SSTORE: update one storage slot for an account. -/
def sstore
    (state : WorldState) (addr : Address) (key : StorageKey) (value : Word256) :
    WorldState :=
  state.setStorage addr key value

end Storage
end EvmAsm.EL
