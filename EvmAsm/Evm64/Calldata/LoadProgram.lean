/-
  EvmAsm.Evm64.Calldata.LoadProgram

  Straight-line byte-window core for the EVM `CALLDATALOAD` opcode
  (GH #104).  This program shape handles the in-bounds 32-byte read:
  pop the calldata offset from the EVM stack, add it to the environment's
  `callDataPtr`, pack four big-endian 8-byte limbs with LBU/SLLI/OR, and
  store the resulting 256-bit word back to the same EVM stack slot.

  The full opcode spec still needs the bounds-check/zero-padding wrapper
  around this core.  Keeping the byte-window core separate gives that
  later proof a compact block to compose.

  Authored by @pirapira; implemented by Codex.
-/

module

public import EvmAsm.Evm64.MLoad.Program
public import EvmAsm.Rv64.SepLogic

@[expose] public section

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/-- Straight-line in-bounds CALLDATALOAD byte-window core.

    `envPtrReg` is expected to hold `env.callDataPtr`.  The program pops
    the low 64-bit offset limb from the EVM stack at `x12`, computes the
    source byte pointer, packs the 32-byte calldata window, and stores
    the result back to the same stack slot.  The stack pointer is
    unchanged because CALLDATALOAD pops one word and pushes one word.

    The instruction sequence is intentionally the same as `evm_mload`;
    CALLDATALOAD supplies `env.callDataPtr` as the base register where
    MLOAD supplies the EVM memory base register. -/
def evm_calldataload_window
    (offReg byteReg accReg addrReg envPtrReg : Reg) : Program :=
  evm_mload offReg byteReg accReg addrReg envPtrReg

/-- Code requirement for `evm_calldataload_window` placed at `base`. -/
abbrev evm_calldataload_window_code
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_calldataload_window offReg byteReg accReg addrReg envPtrReg)

/-- `evm_calldataload_window` is 94 RISC-V instructions. -/
theorem evm_calldataload_window_program_length
    (offReg byteReg accReg addrReg envPtrReg : Reg) :
    (evm_calldataload_window offReg byteReg accReg addrReg envPtrReg).length =
      94 := by
  simpa [evm_calldataload_window] using
    evm_mload_length offReg byteReg accReg addrReg envPtrReg

/-- `evm_calldataload_window` occupies 376 bytes in RV64 code memory. -/
theorem evm_calldataload_window_byte_length
    (offReg byteReg accReg addrReg envPtrReg : Reg) :
    4 * (evm_calldataload_window offReg byteReg accReg addrReg envPtrReg).length =
      376 := by
  rw [evm_calldataload_window_program_length]

/-- Byte offset of the offset-load instruction. -/
theorem evm_calldataload_window_offset_load_byte_off : 4 * 0 = 0 := by
  exact evm_mload_offset_load_byte_off

/-- Byte offset of the source-address ADD instruction. -/
theorem evm_calldataload_window_addr_add_byte_off : 4 * 1 = 4 := by
  exact evm_mload_addr_add_byte_off

/-- Byte offset of the seed LBU inside a byte-pack block. -/
theorem calldataload_byte_pack_seed_byte_off : 4 * 0 = 0 := by
  exact mload_byte_pack_seed_byte_off

/-- Byte offset of repeated LBU instruction `i` inside a byte-pack block. -/
theorem calldataload_byte_pack_lbu_byte_off (i : Nat) :
    4 * (1 + 3 * i) = 4 + 12 * i := by
  exact mload_byte_pack_lbu_byte_off i

/-- Byte offset of repeated SLLI instruction `i` inside a byte-pack block. -/
theorem calldataload_byte_pack_slli_byte_off (i : Nat) :
    4 * (1 + 3 * i + 1) = 8 + 12 * i := by
  exact mload_byte_pack_slli_byte_off i

/-- Byte offset of repeated OR instruction `i` inside a byte-pack block. -/
theorem calldataload_byte_pack_or_byte_off (i : Nat) :
    4 * (1 + 3 * i + 2) = 12 + 12 * i := by
  exact mload_byte_pack_or_byte_off i

/-- Byte offset of the final stack-store inside one output-limb block. -/
theorem calldataload_one_limb_store_byte_off : 4 * 22 = 88 := by
  exact mload_one_limb_store_byte_off

/-- Byte offset of CALLDATALOAD output-limb block `j` within the window core. -/
theorem evm_calldataload_window_limb_block_byte_off (j : Nat) :
    4 * (2 + 23 * j) = 8 + 92 * j := by
  exact evm_mload_limb_block_byte_off j

/-- Byte offset of the final stack-store in output-limb block `j`. -/
theorem evm_calldataload_window_limb_store_byte_off (j : Nat) :
    4 * (2 + 23 * j + 22) = 96 + 92 * j := by
  exact evm_mload_limb_store_byte_off j

/-! ## MLOAD program bridge

The in-bounds CALLDATALOAD byte-window core has the same instruction
shape as MLOAD: both load an offset from `x12`, add a base pointer, pack
the 32-byte big-endian window, and store the result back to the same EVM
stack slot.  CALLDATALOAD supplies `env.callDataPtr` as that base
pointer; MLOAD supplies the EVM memory base pointer.
-/

/-- The CALLDATALOAD byte-window core is program-identical to MLOAD with
    the base register interpreted as the calldata pointer register. -/
theorem evm_calldataload_window_eq_evm_mload
    (offReg byteReg accReg addrReg envPtrReg : Reg) :
    evm_calldataload_window offReg byteReg accReg addrReg envPtrReg =
      evm_mload offReg byteReg accReg addrReg envPtrReg := by
  rfl

/-- CodeReq bridge induced by `evm_calldataload_window_eq_evm_mload`. -/
theorem evm_calldataload_window_code_eq_evm_mload_code
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word) :
    evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base =
      evm_mload_code offReg byteReg accReg addrReg envPtrReg base := by
  unfold evm_calldataload_window_code evm_mload_code
  rw [evm_calldataload_window_eq_evm_mload]

end Calldata
end EvmAsm.Evm64
