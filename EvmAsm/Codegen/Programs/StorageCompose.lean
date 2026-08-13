/-
  EvmAsm.Codegen.Programs.StorageCompose

  Storage-witness composite programs carved out of `StateCompose.lean`
  to keep that file under the hard-cap line limit.  Imports
  `StateCompose` so it can reference the string-constant helpers
  defined there.
-/
import EvmAsm.Codegen.Programs.StateCompose

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## validate_storage_root_in_witness_storage

    Storage-side analog of PR `validate_witness_state_contains_root`.
    Given a parent header RLP, an address, an SSZ `witness.state`
    list section, and an SSZ `witness.storage` list section, walk
    the state trie to the account leaf, extract that account's
    `storage_root` field, and look it up by keccak in
    `witness.storage`.

    The natural prereq for an SLOAD: before descending into the
    storage trie for any slot under `addr`, the storage root node
    has to be present in `witness.storage`. The two well-defined
    edge cases are:
      * `account.storage_root == EMPTY_TRIE_ROOT`
        (`keccak(rlp([])) = 0x56e81f17...`): the account has no
        storage at all; nothing to find. Returned as a distinct
        status from a normal hit so the caller can short-circuit
        any subsequent SLOAD.
      * `storage_root != EMPTY_TRIE_ROOT` but the node isn't in
        `witness.storage`: structural integrity violation -- the
        witness is incomplete relative to the trie commitments in
        the header.

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, K19 `witness_lookup_by_hash`, and an
    inline 4 x u64 compare against the baked-in EMPTY_TRIE_ROOT.

    Calling convention (7 args, fits in a0..a6):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : witness.storage ptr
      a6 (input)  : witness.storage len
      ra (input)  : return

      a0 (output) :
        0 = storage_root found in witness.storage
        1 = account not in state trie
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = account.storage_root == EMPTY_TRIE_ROOT
            (no storage; legitimate, not an error)
        6 = storage_root != EMPTY_TRIE_ROOT but not in
            witness.storage (integrity violation)

    On status 0, the matched offset and length within
    `witness.storage` are written to `vsr_storage_offset` /
    `vsr_storage_length`. The probe BuildUnit copies them to
    OUTPUT + 8 / + 16.
-/
def validateStorageRootInWitnessStorageFunction : String :=
  "validate_storage_root_in_witness_storage:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # witness.storage ptr\n" ++
  "  mv s6, a6                  # witness.storage len\n" ++
  "  # Pre-zero offset/length outputs.\n" ++
  "  la t0, vsr_storage_offset\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la t0, vsr_storage_length\n" ++
  "  sd zero, 0(t0)\n" ++
  "  # Step 1: header.state_root -> vsr_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vsr_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lvsr_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lvsr_ret\n" ++
  ".Lvsr_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, vsr_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s7, vsr_acct_struct\n" ++
  "  mv a5, s7\n" ++
  "  jal ra, account_at_address\n" ++
  "  bnez a0, .Lvsr_ret           # 1/2/3 propagate directly\n" ++
  "  # Step 3: check storage_root == EMPTY_TRIE_ROOT ?\n" ++
  "  la t0, vsr_empty_trie_root\n" ++
  "  ld t1,  0(t0); ld t2, 40(s7); bne t1, t2, .Lvsr_lookup\n" ++
  "  ld t1,  8(t0); ld t2, 48(s7); bne t1, t2, .Lvsr_lookup\n" ++
  "  ld t1, 16(t0); ld t2, 56(s7); bne t1, t2, .Lvsr_lookup\n" ++
  "  ld t1, 24(t0); ld t2, 64(s7); bne t1, t2, .Lvsr_lookup\n" ++
  "  # storage_root == EMPTY_TRIE_ROOT: no storage to find.\n" ++
  "  li a0, 5\n" ++
  "  j .Lvsr_ret\n" ++
  ".Lvsr_lookup:\n" ++
  "  # Step 4: witness_lookup_by_hash(witness.storage, &storage_root).\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  addi a2, s7, 40            # &acct.storage_root\n" ++
  "  la a3, vsr_storage_offset\n" ++
  "  la a4, vsr_storage_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  beqz a0, .Lvsr_ret           # hit -> 0\n" ++
  "  li a0, 6                     # miss -> integrity violation\n" ++
  ".Lvsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_validate_storage_root_in_witness_storage`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len      (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..52+H              : header_rlp
      bytes 52+H..52+H+WS         : witness.state
      bytes 52+H+WS..             : witness.storage
    Output layout:
      bytes  0.. 8 : status (0/1/2/3/4/5/6)
      bytes  8..16 : matched offset in witness.storage (on status 0)
      bytes 16..24 : matched length (on status 0) -/
def ziskValidateStorageRootInWitnessStoragePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  addi a2, t1, 32             # address ptr\n" ++
  "  addi a0, t1, 52             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  add a5, a3, t3              # witness.storage ptr\n" ++
  "  mv a6, t4                   # witness_storage_len\n" ++
  "  jal ra, validate_storage_root_in_witness_storage\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  la t1, vsr_storage_offset; ld t2, 0(t1); sd t2,  8(t0)\n" ++
  "  la t1, vsr_storage_length; ld t2, 0(t1); sd t2, 16(t0)\n" ++
  "  j .Lvsr_pdone\n" ++
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
  headerExtractStateRootFunction ++ "\n" ++
  validateStorageRootInWitnessStorageFunction ++ "\n" ++
  ".Lvsr_pdone:"

def ziskValidateStorageRootInWitnessStorageDataSection : String :=
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
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "vsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "vsr_storage_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "vsr_storage_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "vsr_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"


end EvmAsm.Codegen
