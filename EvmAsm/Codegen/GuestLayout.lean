/-
  EvmAsm.Codegen.GuestLayout

  Hand-written, stable layout *type* for guest programs (GH #10753 /
  bead evm-asm-8fz1p). Programs take a `GuestLayout` parameter and import
  this module instead of the generated `GuestAddrs` instance, so an address
  table regen does not invalidate program modules.

  Prototype scope: only the symbols referenced by `BloomAddValue` (one
  module carrying both difference-based `jalOff` and absolute `laHi`/`laLo`).
  Expand field-by-field as further modules are converted; do not regenerate
  this file on address-only layout drift.
-/

namespace EvmAsm.Codegen

/-- Guest symbol addresses consumed by converted `_prog` bodies. Values are
    supplied at the top-level assembly layer from the generated `GuestAddrs`
    instance; program modules must not import that instance. -/
structure GuestLayout where
  /-- `.data` scratch: keccak digest buffer for `bloom_add_value`. -/
  bav_hash : Nat
  /-- `.text` entry of `bloom_add_value` (PC base for its `la`/`jal`). -/
  bloom_add_value : Nat
  /-- `.text` entry of `zkvm_keccak256` (cross-function `jal` target). -/
  zkvm_keccak256 : Nat

/-- Zero layout for emission-only paths where `emitProgramR` keeps `la`/`jal`
    symbolic via the reloc table (concrete immediates are ignored). -/
def GuestLayout.zero : GuestLayout where
  bav_hash := 0
  bloom_add_value := 0
  zkvm_keccak256 := 0

end EvmAsm.Codegen
