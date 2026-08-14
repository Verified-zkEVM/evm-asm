/-
  EvmAsm.Codegen.Programs.BalAccountPath

  BAL account-change preprocessing for state-root replay. A block access list
  AccountChanges item is RLP-encoded as:
    [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]

  This helper extracts field 0 (the 20-byte account address) and converts it to
  the world-state trie path: bytes_to_nibbles(keccak256(address)). It is the BAL
  analogue of withdrawal_to_path_delta's address-to-path half, but without a
  withdrawal amount.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_path -- BAL AccountChanges RLP -> state-trie path

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = out path ptr (64 bytes, one nibble each)
    a0 (output) = 0 ok / 1 parse fail or address length != 20.

    path = bytes_to_nibbles(keccak256(address)). -/
def balAccountPath_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_path + 24)),
    .BNE .x12 .x0 (68 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_path + 32)),
    .BNE .x11 .x0 (60 : BitVec 13),
    .LI .x7 (20 : Word),
    .BNE .x12 .x7 (52 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bacp_hash (GuestAddrs.bal_account_path + 56)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bacp_hash (GuestAddrs.bal_account_path + 56)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.bal_account_path + 64)),
    .AUIPC .x10 (laHi GuestAddrs.bacp_hash (GuestAddrs.bal_account_path + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bacp_hash (GuestAddrs.bal_account_path + 68)),
    .LI .x11 (32 : Word),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.bal_account_path + 84)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountPath_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountPath_relocs : RelocTable :=
  [ (6, .jal .x1 "rlp_walk_init"),
    (8, .jal .x1 "rlp_walk_next"),
    (14, .la .x12 "bacp_hash"),
    (16, .jal .x1 "zkvm_keccak256"),
    (17, .la .x10 "bacp_hash"),
    (21, .jal .x1 "bytes_to_nibbles") ]

def balAccountPathFunction : String :=
  "bal_account_path:\n" ++ emitProgramR balAccountPath_prog balAccountPath_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountPath_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountPathFunction_eq_prog :
    balAccountPathFunction = "bal_account_path:\n" ++ emitProgramR balAccountPath_prog balAccountPath_relocs := rfl

#guard balAccountPathFunction.startsWith "bal_account_path:\n"
/-- `zisk_bal_account_path`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  AccountChanges RLP length (u64)
      +16 AccountChanges RLP bytes
    Output layout:
      OUTPUT+0 : status (0 ok / 1 fail)
      OUTPUT+8 : path (64 nibble bytes) -/
def ziskBalAccountPathPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account-change RLP length\n" ++
  "  addi a0, t0, 16             # account-change RLP ptr\n" ++
  "  li a2, 0xa0010008           # out path at OUTPUT+8\n" ++
  "  jal ra, bal_account_path\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # status at OUTPUT+0\n" ++
  "  j .Lbacp_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  ".Lbacp_pdone:"

def ziskBalAccountPathDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32"


end EvmAsm.Codegen
