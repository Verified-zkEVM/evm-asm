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
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_path -- BAL AccountChanges RLP -> state-trie path

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = out path ptr (64 bytes, one nibble each)
    a0 (output) = 0 ok / 1 parse fail or address length != 20.

    path = bytes_to_nibbles(keccak256(address)). -/
def balAccountPathFunction : String :=
  "bal_account_path:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # account-change ptr\n" ++
  "  mv s1, a2                   # out path ptr\n" ++
  "  # field 0 = address bytes.\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbacp_fail\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbacp_fail\n" ++
  "  li t2, 20; bne a2, t2, .Lbacp_fail\n" ++
  "  sub a0, a0, a2\n" ++
  "  li a1, 20; la a2, bacp_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, bacp_hash; li a1, 32; mv a2, s1\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  li a0, 0; j .Lbacp_ret\n" ++
  ".Lbacp_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbacp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

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

def ziskBalAccountPathProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountPathPrologue
  dataAsm     := ziskBalAccountPathDataSection
}

end EvmAsm.Codegen
