/-
  EvmAsm.Codegen.Programs.AccountIsEmptyAtBlockHash

  Hash-keyed EIP-161 emptiness predicate. Sibling of the
  EvmCodes EIP-684 variant just landed at block_hash, and of
  the `account_is_empty_at_header_state_root` (under
  StatePredicates).

  Returns 1 iff the account at `address` is present in the
  state trie of the block named by `block_hash` AND is fully
  empty (nonce==0, balance==0, code_hash==EMPTY_CODE_HASH).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_is_empty_at_block_hash_address  (EIP-161 at block_hash)

    EIP-161 emptiness predicate, keyed by block_hash. Same
    distinguishing-row matrix as the at_header_state_root
    sibling -- the only row where this differs from EIP-684
    (`has_code_or_nonce_at_block_hash_address`) is
    `balance only`:

      | account contents       | exists | EIP-684 | EIP-161 |
      |------------------------|--------|---------|---------|
      | fully empty (in trie)  |   1    |    0    |    1    |
      | balance only           |   1    |    0    |    0    |
      | nonce only             |   1    |    1    |    0    |
      | contract (code only)   |   1    |    1    |    0    |
      | (not in trie)          |   0    |    0    |    0    |

    Use cases:
      * Post-execution clearing logic that wants to know if
        an account should be pruned per EIP-161 after touching.
      * Witness-trimming audits: an EIP-161 empty account
        could be omitted from the storage witness without
        affecting consensus.
      * Light-client semantic membership: "is this address
        observably active at this block?" (the negation of
        EIP-161 emptiness, which subsumes both presence and
        non-trivial state).

    Composes K19 + K201 + K28 + nonce==0 AND balance==0 AND
    code_hash==EMPTY_CODE_HASH checks. No new helpers.

    Calling convention (7 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : u64 predicate out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (predicate written; 0 = not-empty, 1 = empty)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = state-trie mpt parse error
        5 = account RLP decode failure
-/
def accountIsEmptyAtBlockHashAddressFunction : String :=
  "account_is_empty_at_block_hash_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # predicate out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, aiebh_match_offset\n" ++
  "  la a4, aiebh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Laiebh_no_match\n" ++
  "  la t0, aiebh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1\n" ++
  "  la t0, aiebh_match_length\n" ++
  "  ld s8, 0(t0)\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, aiebh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Laiebh_walk\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Laiebh_ret\n" ++
  ".Laiebh_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, aiebh_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, aiebh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Laiebh_check\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Laiebh_absent\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Laiebh_ret\n" ++
  ".Laiebh_absent:\n" ++
  "  # account not in trie -> NOT EIP-161 empty (predicate already 0).\n" ++
  "  li a0, 0\n" ++
  "  j .Laiebh_ret\n" ++
  ".Laiebh_check:\n" ++
  "  la t3, aiebh_walked_struct\n" ++
  "  # nonce == 0 ?\n" ++
  "  ld t1, 0(t3)\n" ++
  "  bnez t1, .Laiebh_non_empty\n" ++
  "  # balance == 0 ? (32 BE bytes at +8..+40)\n" ++
  "  ld t1,  8(t3); bnez t1, .Laiebh_non_empty\n" ++
  "  ld t1, 16(t3); bnez t1, .Laiebh_non_empty\n" ++
  "  ld t1, 24(t3); bnez t1, .Laiebh_non_empty\n" ++
  "  ld t1, 32(t3); bnez t1, .Laiebh_non_empty\n" ++
  "  # code_hash == EMPTY_CODE_HASH ? (32 B at +72..+104)\n" ++
  "  la t0, aiebh_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(t3); bne t1, t2, .Laiebh_non_empty\n" ++
  "  ld t1,  8(t0); ld t2, 80(t3); bne t1, t2, .Laiebh_non_empty\n" ++
  "  ld t1, 16(t0); ld t2, 88(t3); bne t1, t2, .Laiebh_non_empty\n" ++
  "  ld t1, 24(t0); ld t2, 96(t3); bne t1, t2, .Laiebh_non_empty\n" ++
  "  # All three empty-conditions hold; predicate := 1.\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Laiebh_ret\n" ++
  ".Laiebh_non_empty:\n" ++
  "  # Predicate stays 0; success.\n" ++
  "  li a0, 0\n" ++
  "  j .Laiebh_ret\n" ++
  ".Laiebh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Laiebh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_account_is_empty_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..56 : block_hash (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..5)
      bytes  8..16 : predicate (u64; 0 = not-empty, 1 = empty) -/
def ziskAccountIsEmptyAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  addi a0, t4, 24             # block_hash ptr\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # predicate out\n" ++
  "  jal ra, account_is_empty_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laiebh_pdone\n" ++
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
  accountIsEmptyAtBlockHashAddressFunction ++ "\n" ++
  ".Laiebh_pdone:"

def ziskAccountIsEmptyAtBlockHashAddressDataSection : String :=
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
  ".balign 8\n" ++
  "aiebh_match_offset:\n" ++
  "  .zero 8\n" ++
  "aiebh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aiebh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "aiebh_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "aiebh_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
