/-
  EvmAsm.Codegen.Programs.ExtcodehashAtBlockHash

  Hash-keyed EIP-1052 EXTCODEHASH primitive. Mirrors the
  existing `extcodehash_at_header_state_root` (under
  EvmOpcodes) but takes a `block_hash` as the key instead of
  raw header bytes.

  Pipeline:
    witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
    h -> header_extract_state_root                     [K201]
    state_root + address -> account_at_address         [K28]
    EIP-1052: if account absent OR account is EIP-161 empty
              return 0 (32 zero bytes)
              else return account.code_hash

  Distinct from the plain `code_hash_at_block_hash_address`
  extractor in the EIP-1052 emptiness collapse: a fully-empty
  account has its EIP-1052 hash mapped to 0, not to the raw
  EMPTY_CODE_HASH stored in the trie.

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

/-! ## extcodehash_at_block_hash_address  (EIP-1052 at block_hash)

    Returns the EIP-1052 EXTCODEHASH value: a 32-byte hash
    that is `account.code_hash` when the account exists and
    is NOT EIP-161 empty, otherwise zero.

    The EIP-1052 emptiness collapse distinguishes this
    primitive from a plain `code_hash_at_block_hash_address`
    extractor:

      | account contents       | code_hash extract | EXTCODEHASH |
      |------------------------|-------------------|-------------|
      | fully empty (in trie)  | EMPTY_CODE_HASH   | 0           |
      | nonce only             | EMPTY_CODE_HASH   | EMPTY_CODE_HASH |
      | balance only           | EMPTY_CODE_HASH   | EMPTY_CODE_HASH |
      | contract               | k256(code)        | k256(code)  |
      | (not in trie)          | 0 (spec default)  | 0           |

    Use cases:
      * EXTCODEHASH opcode replay against a historical block
        keyed by hash.
      * Light-client semantic membership predicate without
        needing to chase witness.codes (saves a K19 lookup).

    Composes K19 (witness.headers by block_hash) + K201 + K28
    + EIP-161-emptiness check. No new helpers.

    Calling convention (7 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 32-byte EXTCODEHASH out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (out buffer holds the EIP-1052 result;
            may be 0 for missing/empty)
        1 = block_hash not in witness.headers
        2 = matched header parse / state_root size fail
        3 = state-trie mpt parse error
        4 = account RLP decode failure
-/
def extcodehashAtBlockHashAddressFunction : String :=
  "extcodehash_at_block_hash_address:\n" ++
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
  "  mv s6, a6                  # 32-byte output ptr\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, eabh_match_offset\n" ++
  "  la a4, eabh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Leabh_no_match\n" ++
  "  la t0, eabh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1\n" ++
  "  la t0, eabh_match_length\n" ++
  "  ld s8, 0(t0)\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, eabh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Leabh_walk\n" ++
  "  li a0, 2\n" ++
  "  j .Leabh_ret\n" ++
  ".Leabh_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, eabh_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, eabh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Leabh_check_empty\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Leabh_success_zero\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Leabh_ret\n" ++
  ".Leabh_success_zero:\n" ++
  "  # absent -> EIP-1052 result is 0; out buffer already zeroed.\n" ++
  "  li a0, 0\n" ++
  "  j .Leabh_ret\n" ++
  ".Leabh_check_empty:\n" ++
  "  # nonce == 0 ?\n" ++
  "  la t3, eabh_walked_struct\n" ++
  "  ld t1, 0(t3)\n" ++
  "  bnez t1, .Leabh_write_code_hash\n" ++
  "  # balance == 0 ?\n" ++
  "  ld t1,  8(t3); bnez t1, .Leabh_write_code_hash\n" ++
  "  ld t1, 16(t3); bnez t1, .Leabh_write_code_hash\n" ++
  "  ld t1, 24(t3); bnez t1, .Leabh_write_code_hash\n" ++
  "  ld t1, 32(t3); bnez t1, .Leabh_write_code_hash\n" ++
  "  # code_hash == EMPTY_CODE_HASH ?\n" ++
  "  la t0, eabh_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(t3); bne t1, t2, .Leabh_write_code_hash\n" ++
  "  ld t1,  8(t0); ld t2, 80(t3); bne t1, t2, .Leabh_write_code_hash\n" ++
  "  ld t1, 16(t0); ld t2, 88(t3); bne t1, t2, .Leabh_write_code_hash\n" ++
  "  ld t1, 24(t0); ld t2, 96(t3); bne t1, t2, .Leabh_write_code_hash\n" ++
  "  # EIP-161 empty; EIP-1052 result is 0; out buffer already zero.\n" ++
  "  li a0, 0\n" ++
  "  j .Leabh_ret\n" ++
  ".Leabh_write_code_hash:\n" ++
  "  # Non-empty account; copy code_hash to output.\n" ++
  "  ld t1, 72(t3); sd t1,  0(s6)\n" ++
  "  ld t1, 80(t3); sd t1,  8(s6)\n" ++
  "  ld t1, 88(t3); sd t1, 16(s6)\n" ++
  "  ld t1, 96(t3); sd t1, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Leabh_ret\n" ++
  ".Leabh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Leabh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_extcodehash_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..56 : block_hash (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..4)
      bytes  8..40 : EXTCODEHASH (32 B; 0 on missing/empty) -/
def ziskExtcodehashAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  addi a0, t4, 24             # block_hash ptr\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # 32 B output ptr\n" ++
  "  jal ra, extcodehash_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Leabh_pdone\n" ++
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
  extcodehashAtBlockHashAddressFunction ++ "\n" ++
  ".Leabh_pdone:"

def ziskExtcodehashAtBlockHashAddressDataSection : String :=
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
  "eabh_match_offset:\n" ++
  "  .zero 8\n" ++
  "eabh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "eabh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "eabh_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eabh_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
