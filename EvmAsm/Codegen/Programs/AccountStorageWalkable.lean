/-
  EvmAsm.Codegen.Programs.AccountStorageWalkable

  Fused precondition predicate: given a trusted state_root
  and address, walk to find the account's storage_root,
  then check whether that storage_root is reachable in
  witness.storage.

  Single-call fail-fast for "before I attempt to walk this
  account's storage, is the walk even possible with the
  witness I have?"

  Composes K28 + K19.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_storage_walkable_at_state_root

    Pipeline:
      state_root + address -> account.storage_root    [K28]
      storage_root + witness.storage -> presence?     [K19]

    Returns:
      * walkable (u64; 0 or 1): is the account's
        storage_root present as a node in witness.storage?

    The primitive distinguishes failure modes (account
    absent, account present with EMPTY_TRIE storage, walk
    parse error, etc.) via status codes. The walkable flag
    is meaningful only when status == 0.

    Use cases:
      * Cheap precondition for #7191 (storage slot
        inclusion proof verify): if the account exists but
        storage_root isn't in witness.storage, no slot proof
        can succeed -- fail fast at zero MPT-walk cost.
      * Witness completeness audit: detect partial witnesses
        that have the state portion but lack the storage
        nodes for a specific account.
      * EOA detection (specific case): for an EOA with
        EMPTY_TRIE storage_root, this primitive returns
        walkable = 0 distinctly (status 1) -- callers can
        skip the storage walk entirely.

    Calling convention (7 args):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : witness.storage ptr
      a5 (input)  : witness.storage len
      a6 (input)  : u64 walkable out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (walkable flag valid; 0 means
            storage_root not in witness.storage, 1 means
            it is reachable)
        1 = account absent in state trie (walkable = 0;
            spec default storage_root = EMPTY_TRIE_ROOT
            which never appears as a witness.storage entry)
        2 = state-trie mpt parse error
        3 = account RLP decode failure
-/
def accountStorageWalkableAtStateRootFunction : String :=
  "account_storage_walkable_at_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # witness.state ptr\n" ++
  "  mv s3, a3                  # witness.state len\n" ++
  "  mv s4, a4                  # witness.storage ptr\n" ++
  "  mv s5, a5                  # witness.storage len\n" ++
  "  mv s6, a6                  # walkable out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # Step 1: account_at_address.\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s2                  # witness.state ptr\n" ++
  "  mv a4, s3                  # witness.state len\n" ++
  "  la a5, aswr_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lawsr_check_storage\n" ++
  "  # K28 1=absent, 2=mpt fail, 3=decode fail.\n" ++
  "  # Propagate directly (codes happen to line up: 1/2/3).\n" ++
  "  j .Laswr_ret\n" ++
  ".Lawsr_check_storage:\n" ++
  "  # Step 2: K19 over witness.storage with storage_root.\n" ++
  "  la t0, aswr_walked_struct\n" ++
  "  addi t0, t0, 40            # storage_root field\n" ++
  "  mv a0, s4                  # section ptr\n" ++
  "  mv a1, s5                  # section_len\n" ++
  "  mv a2, t0                  # target_hash\n" ++
  "  la a3, aswr_match_offset\n" ++
  "  la a4, aswr_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Laswr_not_reachable\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s6)\n" ++
  ".Laswr_not_reachable:\n" ++
  "  li a0, 0\n" ++
  ".Laswr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_storage_walkable_at_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..24 : witness_storage_len (u64 LE)
      bytes 24..56 : state_root (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.state ++ witness.storage
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : walkable (u64; 0 or 1) -/
def ziskAccountStorageWalkableAtStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a3, 8(t4)                # witness_state_len\n" ++
  "  ld a5, 16(t4)               # witness_storage_len\n" ++
  "  addi a0, t4, 24             # state_root ptr\n" ++
  "  addi a1, t4, 56             # address ptr\n" ++
  "  addi a2, t4, 76             # witness.state ptr\n" ++
  "  add  a4, a2, a3             # witness.storage ptr\n" ++
  "  li a6, 0xa0010008           # walkable out\n" ++
  "  jal ra, account_storage_walkable_at_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laswr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  accountStorageWalkableAtStateRootFunction ++ "\n" ++
  ".Laswr_pdone:"

def ziskAccountStorageWalkableAtStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "aswr_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aswr_match_offset:\n" ++
  "  .zero 8\n" ++
  "aswr_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
