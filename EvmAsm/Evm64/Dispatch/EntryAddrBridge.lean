/-
  EvmAsm.Evm64.Dispatch.EntryAddrBridge

  Slice 3c of GH #106 (parent `evm-asm-77w8s`, this slice
  `evm-asm-b11gg`).  Pure address-form bridge between

    * the post-state of `evm_dispatch_entry_addr_spec_within` (slice
      3b), where `rOp` holds `(opcodeByte <<< 3) + tableBase`; and
    * the entry cell exposed by `dispatchTableIs_split` (slice 3a),
      whose address is `tableBase + BitVec.ofNat 64 (8 * opcode.val)`.

  Both forms denote the same Word, but the eventual `dispatch_spec`
  compose proof needs the equality as a small, reusable rewrite to
  align EntrySpec's output with TailSpec's input (and with the LD step
  consuming the split table cell).

  This is a self-contained Word arithmetic lemma: no proof-state
  dependency, no `cpsTriple`, just a `BitVec 64` calculation. Splitting
  it out keeps the `dispatch_spec` slice (`evm-asm-afkny`) lean.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs GH #106, beads `evm-asm-b11gg`, parent `evm-asm-77w8s`.
-/

-- Only `Word` (= `BitVec 64`) and standard `BitVec` lemmas are used here; pull
-- them in directly via `EvmAsm.Rv64.Program` (which transitively imports
-- `EvmAsm.Rv64.Basic` where the `Word` notation lives) instead of the larger
-- `EvmAsm.Evm64.Dispatch.Program`. Slice of #1045.
module

public import EvmAsm.Rv64.Program

@[expose] public section

namespace EvmAsm.Evm64
namespace Dispatch

open EvmAsm.Rv64

/-- Bridge between EntrySpec output form and `dispatchTableIs_split`
    cell-address form.

    For any 64-bit `tableBase` and any byte `b < 256`,

        ((BitVec.ofNat 64 b) <<< 3) + tableBase
          = tableBase + BitVec.ofNat 64 (8 * b)

    This is a structural rewrite used only to align the `rOp`
    register-state from `evm_dispatch_entry_addr_spec_within` with the
    table-entry address `tableBase + BitVec.ofNat 64 (8 * opcode.val)`
    produced by `dispatchTableIs_split`. -/
theorem entry_addr_bridge (tableBase : Word) (b : Nat) (hb : b < 256) :
    ((BitVec.ofNat 64 b) <<< (3 : Nat)) + tableBase
      = tableBase + BitVec.ofNat 64 (8 * b) := by
  rw [BitVec.add_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hb' : b < 2 ^ 64 := by omega
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hb',
        Nat.shiftLeft_eq, Nat.mul_comm]

/-- `Fin 256` packaging of `entry_addr_bridge`: bridges the form of
    `dispatchTableIs_split` (which uses `opcode.val` from a `Fin 256`)
    with `EntrySpec`'s output form. -/
theorem entry_addr_bridge_fin (tableBase : Word) (opcode : Fin 256) :
    ((BitVec.ofNat 64 opcode.val) <<< (3 : Nat)) + tableBase
      = tableBase + BitVec.ofNat 64 (8 * opcode.val) :=
  entry_addr_bridge tableBase opcode.val opcode.isLt

end Dispatch
end EvmAsm.Evm64
