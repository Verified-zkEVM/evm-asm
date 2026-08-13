/-
  EvmAsm.Codegen.Programs.HasCodeOrNonceAtBlockHash

  Hash-keyed EIP-684 CREATE-collision predicate.

  Mirrors `has_code_or_nonce_at_header_state_root` (under
  EvmCodes) but keyed by `block_hash`. Returns 1 iff the
  account at `address` in the state trie of the block named
  by `block_hash` has nonce != 0 OR code_hash != EMPTY_CODE_HASH.

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

/-! ## has_code_or_nonce_at_block_hash_address  (EIP-684 at block_hash)

    EIP-684 CREATE-collision predicate, keyed by block_hash
    rather than by raw header bytes (the version that already
    exists under EvmCodes). Returns 1 iff the account exists
    in the state trie at `block_hash` AND has either
    `nonce != 0` or `code_hash != EMPTY_CODE_HASH`.

    Spec-distinguishing row matrix (vs the existing
    `account_exists_at_block_hash_address` and the upcoming
    `account_is_empty_at_block_hash_address`):

      | account at block_hash       | exists | EIP-684 | EIP-161 |
      |-----------------------------|--------|---------|---------|
      | fully empty (in trie)       |   1    |    0    |    1    |
      | balance only                |   1    |    0    |    0    |
      | nonce only                  |   1    |    1    |    0    |
      | contract (code only)        |   1    |    1    |    0    |
      | (not in trie)               |   0    |    0    |    0    |

    Use cases:
      * CREATE / CREATE2 collision guard: before allowing a
        contract creation at `address` against a historical
        block, this primitive answers the EIP-684 question.
      * Bridge cross-check: a counter-party claims address X
        was suitable for deployment at block_hash Y -- verify
        independently.

    Composes K19 + K201 + K28 + 5 u64 compares against the
    EMPTY_CODE_HASH constant. No new helpers.

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
        0 = success (predicate written; 0 = no collision, 1 = collision)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = state-trie mpt parse error
        5 = account RLP decode failure
-/
def hasCodeOrNonceAtBlockHashAddressFunction : String :=
  "has_code_or_nonce_at_block_hash_address:\n" ++
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
  "  la a3, hcobh_match_offset\n" ++
  "  la a4, hcobh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lhcobh_no_match\n" ++
  "  la t0, hcobh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1\n" ++
  "  la t0, hcobh_match_length\n" ++
  "  ld s8, 0(t0)\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, hcobh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lhcobh_walk\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lhcobh_ret\n" ++
  ".Lhcobh_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, hcobh_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, hcobh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lhcobh_check\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lhcobh_no_collision\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Lhcobh_ret\n" ++
  ".Lhcobh_check:\n" ++
  "  # nonce != 0 ?\n" ++
  "  la t3, hcobh_walked_struct\n" ++
  "  ld t1, 0(t3)\n" ++
  "  bnez t1, .Lhcobh_collide\n" ++
  "  # code_hash != EMPTY_CODE_HASH ?\n" ++
  "  la t0, hcobh_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(t3); bne t1, t2, .Lhcobh_collide\n" ++
  "  ld t1,  8(t0); ld t2, 80(t3); bne t1, t2, .Lhcobh_collide\n" ++
  "  ld t1, 16(t0); ld t2, 88(t3); bne t1, t2, .Lhcobh_collide\n" ++
  "  ld t1, 24(t0); ld t2, 96(t3); bne t1, t2, .Lhcobh_collide\n" ++
  "  # nonce == 0 AND code_hash == EMPTY -> no collision.\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcobh_ret\n" ++
  ".Lhcobh_collide:\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcobh_ret\n" ++
  ".Lhcobh_no_collision:\n" ++
  "  # account not in trie -> no collision; predicate already 0.\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcobh_ret\n" ++
  ".Lhcobh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lhcobh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_has_code_or_nonce_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..56 : block_hash (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..5)
      bytes  8..16 : predicate (u64; 0 = no collision, 1 = collision) -/
def ziskHasCodeOrNonceAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  addi a0, t4, 24             # block_hash ptr\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # predicate out\n" ++
  "  jal ra, has_code_or_nonce_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhcobh_pdone\n" ++
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
  hasCodeOrNonceAtBlockHashAddressFunction ++ "\n" ++
  ".Lhcobh_pdone:"

def ziskHasCodeOrNonceAtBlockHashAddressDataSection : String :=
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
  "hcobh_match_offset:\n" ++
  "  .zero 8\n" ++
  "hcobh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "hcobh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "hcobh_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "hcobh_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
