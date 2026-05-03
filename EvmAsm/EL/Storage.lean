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

@[simp] theorem sload_empty (addr : Address) (key : StorageKey) :
    sload WorldState.empty addr key = 0 := rfl

@[simp] theorem sload_sstore_same
    (state : WorldState) (addr : Address) (key : StorageKey) (value : Word256) :
    sload (sstore state addr key value) addr key = value := by
  simp [sload, sstore]

theorem sload_sstore_addr_ne
    (state : WorldState) {addr other : Address} (key key' : StorageKey) (value : Word256)
    (h_ne : other ≠ addr) :
    sload (sstore state addr key value) other key' = sload state other key' := by
  simp [sload, sstore, WorldState.getStorage_setStorage_addr_ne, h_ne]

theorem sload_sstore_key_ne
    (state : WorldState) (addr : Address) {key other : StorageKey} (value : Word256)
    (h_ne : other ≠ key) :
    sload (sstore state addr key value) addr other = sload state addr other := by
  simp [sload, sstore, WorldState.getStorage_setStorage_key_ne, h_ne]

/-- SSTORE does not change account metadata. It only updates the storage map in
    this pure model. -/
theorem getAccount_sstore
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) (value : Word256) :
    WorldState.getAccount (sstore state storageAddr key value) addr =
      WorldState.getAccount state addr := rfl

end Storage
end EvmAsm.EL
